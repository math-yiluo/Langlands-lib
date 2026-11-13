import Langlands.GroupScheme.Rational.DynamicRadicalRootGeneration
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # Rational points of an intersection of two dynamic radicals, bounded by roots -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Let `i : S ⟶ G` be a homomorphism from a split torus into a smooth connected affine group
and `mu, ν, κ` cocharacters of `S`. If every relative root positive on `ν` and on `mu` is positive
on `κ`, then `U(mu)(k) ∩ U(ν)(k) ⊆ U(κ)(k)`. -/
theorem dynamicUnipotent_inf_le_of_positiveRoots
    (hGs : Smooth G.X.hom) (hGc : ConnectedSpace G.X.left)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (mu ν κ : cocharacterLattice S)
    (hroots : ∀ β ∈ positiveRelativeRoots i ν,
      0 < latticePairing S β mu → 0 < latticePairing S β κ) :
    (Dynamic.unipotent (CommGroupScheme.groupHom mu ≫ i)).carrier (Over.mk (𝟙 _)) ⊓
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) ≤
      (Dynamic.unipotent (CommGroupScheme.groupHom κ ≫ i)).carrier (Over.mk (𝟙 _)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let b := AutomorphicAction.conjugation i
  let A := positiveSemigroup ν
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k G hGs inferInstance S hS b A
  have hzero : (0 : characterLattice S) ∉ A := by
    change ¬ 0 < latticePairing S 0 ν
    simp
  obtain ⟨hUu, _⟩ := hUnip U jU hjU hzero
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let : Smooth U.X.hom := hUs
  let : ConnectedSpace U.X.left := hUc
  let c := b.onRepresentedSubgroup jU hjU hStable
  have hequiv : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (x : T ⟶ U.X), c.act s x ≫ jU.hom.hom = b.act s (x ≫ jU.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp jU hjU hStable s x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b A := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots i ν := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup semigroupRealization hGs hS i ν
  -- the two blocks: roots of `U(ν)` positive, resp. nonpositive, on `mu`
  let Ψ₀ : Set (characterLattice S) :=
    {β | β ∈ positiveRelativeRoots i ν ∧ 0 < latticePairing S β mu}
  let Ψ₁ : Set (characterLattice S) :=
    {β | β ∈ positiveRelativeRoots i ν ∧ latticePairing S β mu ≤ 0}
  let Ψ : Fin 2 → Set (characterLattice S) := ![Ψ₀, Ψ₁]
  have hcl₀ : AddSubsemigroup.closure Ψ₀ ≤ positiveSemigroup mu :=
    AddSubsemigroup.closure_le.mpr fun β hβ => hβ.2
  have hcl₁ : AddSubsemigroup.closure Ψ₁ ≤ nonnegativeSemigroup (-mu) :=
    AddSubsemigroup.closure_le.mpr fun β hβ => by
      change 0 ≤ latticePairing S β (-mu)
      rw [map_neg]
      exact neg_nonneg.mpr hβ.2
  have hclν (r : Fin 2) : AddSubsemigroup.closure (Ψ r) ≤ A := by
    apply AddSubsemigroup.closure_le.mpr
    fin_cases r
    · exact fun β hβ => hβ.1.2
    · exact fun β hβ => hβ.1.2
  have hcover : (⋃ r, Ψ r) = actionWeightSupport c ⊤ := by
    rw [hsupport]
    ext β
    simp only [Set.mem_iUnion, Fin.exists_fin_two, Ψ, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      by_cases hmu : 0 < latticePairing S β mu
      · exact Or.inl ⟨h, hmu⟩
      · exact Or.inr ⟨h, not_lt.mp hmu⟩
  have hdis₀₁ : Disjoint Ψ₀ (AddSubsemigroup.closure Ψ₁ : Set (characterLattice S)) := by
    rw [Set.disjoint_left]
    intro β h₀ h₁
    have h := hcl₁ h₁
    change 0 ≤ latticePairing S β (-mu) at h
    rw [map_neg] at h
    linarith [h₀.2]
  have hdis₁₀ : Disjoint Ψ₁ (AddSubsemigroup.closure Ψ₀ : Set (characterLattice S)) := by
    rw [Set.disjoint_left]
    intro β h₁ h₀
    have h := hcl₀ h₀
    change 0 < latticePairing S β mu at h
    linarith [h₁.2]
  have hcross : ∀ r s : Fin 2, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S)) := by
    intro r s hrs
    fin_cases r <;> fin_cases s
    · exact absurd rfl hrs
    · exact hdis₀₁
    · exact hdis₁₀
    · exact absurd rfl hrs
  have hdis : ∀ r s : Fin 2, r ≠ s → Disjoint (Ψ r) (Ψ s) := fun r s hrs =>
    (hcross r s hrs).mono_right AddSubsemigroup.subset_closure
  obtain ⟨H, jH, hH, hIso⟩ :=
    hasOrderedSemigroupProducts_of_unipotent c hS hUu 2 Ψ hcover hdis hcross
  have hsemigroup (r : Fin 2) :
      (semigroupSubgroup c (AddSubsemigroup.closure (Ψ r))).map jU =
        semigroupSubgroup b (AddSubsemigroup.closure (Ψ r)) := by
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (hclν r)
  have hfactor (r : Fin 2) :
      (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).IsRepresentedBy (jH r ≫ jU) := by
    rw [← hsemigroup r]
    exact (hH r).1.comp hjU
  have hDyn := dynamicSemigroupComparison k G hGs inferInstance hGc S hS i
  rintro g ⟨hgmu, hgν⟩
  have hgA : g ∈ (semigroupSubgroup b A).carrier (Over.mk (𝟙 _)) := (hDyn ν).2.2 ▸ hgν
  let := hIso
  let gU : rationalPoints U := (hjU.pointsEquiv _).symm ⟨g, hgA⟩
  let x : rationalPoints (∏ᶜ H) := gU ≫ inv (orderedMultiplication jH)
  have hx : x ≫ orderedMultiplication (fun r => jH r ≫ jU) = g := by
    rw [← orderedMultiplication_comp jH jU]
    simp only [x, Category.assoc, IsIso.inv_hom_id_assoc]
    exact hjU.pointsEquiv_symm_comp _
  rw [comp_orderedMultiplication] at hx
  unfold orderedPoints at hx
  set y : Fin 2 → rationalPoints G := fun r =>
    finiteProductPointsEquiv H _ x r ≫ (jH r ≫ jU).hom.hom with hy
  have hymem (r : Fin 2) :
      y r ∈ (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).carrier (Over.mk (𝟙 _)) :=
    ((hfactor r).pointsEquiv _ (finiteProductPointsEquiv H _ x r)).property
  have hprod : y 0 * y 1 = g := by
    rw [← hx]
    simp [List.ofFn_succ, y]
  -- the first factor lies in `U(κ)` and in `U(mu)`
  have hy₀κ : y 0 ∈ (Dynamic.unipotent (CommGroupScheme.groupHom κ ≫ i)).carrier
      (Over.mk (𝟙 _)) := by
    rw [(hDyn κ).2.2]
    exact semigroupSubgroup_mono b
      (AddSubsemigroup.closure_le.mpr fun β hβ => hroots β hβ.1 hβ.2) _ (hymem 0)
  have hy₀mu : y 0 ∈ (Dynamic.unipotent (CommGroupScheme.groupHom mu ≫ i)).carrier
      (Over.mk (𝟙 _)) := by
    rw [(hDyn mu).2.2]
    exact semigroupSubgroup_mono b hcl₀ _ (hymem 0)
  -- the second factor lies in `P(-mu) ∩ U(mu)`, hence is trivial
  have hy₁P : y 1 ∈ (Dynamic.parabolic (CommGroupScheme.groupHom (-mu) ≫ i)).carrier
      (Over.mk (𝟙 _)) := by
    rw [(hDyn (-mu)).1]
    exact semigroupSubgroup_mono b hcl₁ _ (hymem 1)
  have hy₁U : y 1 ∈ (Dynamic.unipotent (CommGroupScheme.groupHom mu ≫ i)).carrier
      (Over.mk (𝟙 _)) := by
    have h : y 1 = (y 0)⁻¹ * g := by
      rw [← hprod, inv_mul_cancel_left]
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hy₀mu) hgmu
  have hopp : CommGroupScheme.groupHom mu ≫ i =
      Dynamic.oppositeCocharacter (CommGroupScheme.groupHom (-mu) ≫ i) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter, neg_neg]
  rw [hopp] at hy₁U
  have hy₁ : y 1 = 1 :=
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic _ hy₁U hy₁P
  rw [← hprod, hy₁, mul_one]
  exact hy₀κ

end Langlands.GroupScheme.RelativeRoot
