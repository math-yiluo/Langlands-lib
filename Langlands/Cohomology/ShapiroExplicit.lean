import Langlands.Cohomology.Tate.ShiftDefinitions
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # Shapiro's lemma through restriction and evaluation

For a subgroup `S ≤ G` and an `S`-representation `A`, the map
`Hⁿ(G, Coind_S^G A) ⟶ Hⁿ(S, A)` obtained by restricting cochains to `S` and evaluating
the coinduced coefficients at the identity is an isomorphism in every degree.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Shapiro

set_option backward.isDefEq.respectTransparency false

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

/-- Evaluation at the identity, `Res_S (Coind_S^G A) ⟶ A`, `f ↦ f 1`. -/
def coindEval (A : Rep.{u} k S) : Rep.res S.subtype (Rep.coind S.subtype A) ⟶ A :=
  Rep.ofHom ⟨(LinearMap.proj (1 : G)).comp (A.ρ.coindV S.subtype).subtype, fun s => by
    ext f
    change f.1 (1 * (s : G)) = A.ρ s (f.1 1)
    rw [one_mul, ← f.2 s 1, mul_one]
    rfl⟩

@[simp]
lemma coindEval_hom_apply (A : Rep.{u} k S) (f : Rep.coind S.subtype A) :
    (coindEval S A).hom f = f.1 1 := rfl

/-- The explicit Shapiro map `Hⁿ(G, Coind_S^G A) ⟶ Hⁿ(S, A)`: restriction of cochains to
`S` followed by evaluation of the coefficients at the identity. -/
abbrev shapiroMap (A : Rep.{u} k S) (n : ℕ) :
    groupCohomology (Rep.coind S.subtype A) n ⟶ groupCohomology A n :=
  groupCohomology.map S.subtype (coindEval S A) n

/-- On cochains, the explicit Shapiro map commutes with coefficient maps. -/
lemma cochainsMap_coindEval_naturality {A B : Rep.{u} k S} (φ : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) (Rep.coindMap S.subtype φ) ≫
        groupCohomology.cochainsMap S.subtype (coindEval S B) =
      groupCohomology.cochainsMap S.subtype (coindEval S A) ≫
        groupCohomology.cochainsMap (MonoidHom.id S) φ :=
  rfl

/-- The explicit Shapiro map is natural in the coefficients. -/
lemma shapiroMap_naturality {A B : Rep.{u} k S} (φ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (Rep.coindMap S.subtype φ) n ≫ shapiroMap S B n =
      shapiroMap S A n ≫ groupCohomology.map (MonoidHom.id S) φ n := by
  simp only [groupCohomology.map, ← HomologicalComplex.homologyMap_comp,
    cochainsMap_coindEval_naturality]

/-- The `G`-invariants of `Coind_S^G A` are the constant functions with value in `A^S`. -/
def coindInvariantsEquiv (A : Rep.{u} k S) :
    (Rep.coind S.subtype A).ρ.invariants ≃ₗ[k] A.ρ.invariants where
  toFun f := ⟨f.1.1 1, fun s => by
    have h := congrArg (fun x => x.1 (1 : G)) (f.2 (s : G))
    change f.1.1 (1 * (s : G)) = f.1.1 1 at h
    rw [one_mul] at h
    refine (f.1.2 s 1).symm.trans ?_
    rw [mul_one]
    exact h⟩
  invFun a := ⟨⟨fun _ => a.1, fun s _ => (a.2 s).symm⟩, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h := congrArg (fun x => x.1 (1 : G)) (f.2 g)
    change f.1.1 (1 * g) = f.1.1 1 at h
    rw [one_mul] at h
    exact h.symm
  right_inv _ := rfl

lemma shapiroMap_zero_comp_H0Iso (A : Rep.{u} k S) :
    shapiroMap S A 0 ≫ (groupCohomology.H0Iso A).hom =
      (groupCohomology.H0Iso (Rep.coind S.subtype A)).hom ≫
        (coindInvariantsEquiv S A).toModuleIso.hom := by
  rw [← cancel_mono (groupCohomology.shortComplexH0 A).f, Category.assoc,
    groupCohomology.map_H0Iso_hom_f]
  rfl

instance isIso_shapiroMap_zero (A : Rep.{u} k S) : IsIso (shapiroMap S A 0) := by
  have h : shapiroMap S A 0 = (groupCohomology.H0Iso (Rep.coind S.subtype A)).hom ≫
      (coindInvariantsEquiv S A).toModuleIso.hom ≫ (groupCohomology.H0Iso A).inv := by
    rw [← Category.assoc, ← shapiroMap_zero_comp_H0Iso, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [h]
  infer_instance

/-- Coinduction from a subgroup carries short exact sequences to short exact sequences. -/
lemma coind_shortExact {X : ShortComplex (Rep.{u} k S)} (hX : X.ShortExact) :
    (X.map (Rep.coindFunctor k S.subtype)).ShortExact := by
  have := hX.mono_f
  have := hX.epi_g
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _
        (KernelFork.mapIsLimit _ hX.fIsKernel (Rep.coindFunctor k S.subtype))
      mono_f := (inferInstance : Mono ((Rep.coindFunctor k S.subtype).map X.f))
      epi_g := (inferInstance : Epi ((Rep.coindFunctor k S.subtype).map X.g)) }

/-- A representation coinduced from the trivial subgroup is acyclic. -/
lemma isZero_coinduced (A : Rep.{u} k S) (n : ℕ) :
    IsZero (groupCohomology (Langlands.Tate.coinduced A) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
    (Rep.res (⊥ : Subgroup S).subtype A) n).of_iso
      (groupCohomology.coindIso (Rep.res (⊥ : Subgroup S).subtype A) (n + 1))

/-- Coinduction to `G` preserves vanishing of cohomology (by Mathlib's Shapiro isomorphism). -/
lemma isZero_coind_of_isZero {B : Rep.{u} k S} {n : ℕ} (h : IsZero (groupCohomology B n)) :
    IsZero (groupCohomology (Rep.coind S.subtype B) n) :=
  h.of_iso (groupCohomology.coindIso B n)

/-- The cochain-level explicit Shapiro maps on the coinduced sequence of `A`. -/
def shapiroCochainsSequenceMap (X : ShortComplex (Rep.{u} k S)) :
    (X.map (Rep.coindFunctor k S.subtype)).map (groupCohomology.cochainsFunctor k G) ⟶
      X.map (groupCohomology.cochainsFunctor k S) where
  τ₁ := groupCohomology.cochainsMap S.subtype (coindEval S X.X₁)
  τ₂ := groupCohomology.cochainsMap S.subtype (coindEval S X.X₂)
  τ₃ := groupCohomology.cochainsMap S.subtype (coindEval S X.X₃)
  comm₁₂ := cochainsMap_coindEval_naturality S X.f
  comm₂₃ := cochainsMap_coindEval_naturality S X.g

/-- The explicit Shapiro maps commute with the connecting homomorphisms. -/
lemma shapiroMap_δ {X : ShortComplex (Rep.{u} k S)} (hX : X.ShortExact) (n : ℕ) :
    groupCohomology.δ (coind_shortExact S hX) n (n + 1) rfl ≫ shapiroMap S X.X₁ (n + 1) =
      shapiroMap S X.X₃ n ≫ groupCohomology.δ hX n (n + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality (shapiroCochainsSequenceMap S X)
    (groupCohomology.map_cochainsFunctor_shortExact (coind_shortExact S hX))
    (groupCohomology.map_cochainsFunctor_shortExact hX) n (n + 1) rfl

/-- **Shapiro's lemma**, explicit form: restriction to `S` followed by evaluation at the
identity is an isomorphism `Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)` in every degree. -/
theorem isIso_shapiroMap (A : Rep.{u} k S) (n : ℕ) : IsIso (shapiroMap S A n) := by
  induction n generalizing A with
  | zero => infer_instance
  | succ n ih =>
    let X := Langlands.Tate.shiftUpSequence A
    have hX : X.ShortExact := Langlands.Tate.shiftUpSequence_shortExact A
    have hY := coind_shortExact S hX
    have hδX : Epi (groupCohomology.δ hX n (n + 1) rfl) :=
      groupCohomology.epi_δ_of_isZero hX n (isZero_coinduced S A n)
    have hδY : Epi (groupCohomology.δ hY n (n + 1) rfl) :=
      groupCohomology.epi_δ_of_isZero hY n (isZero_coind_of_isZero S (isZero_coinduced S A n))
    have hcomm := shapiroMap_δ S hX n
    have hepi : Epi (shapiroMap S A (n + 1)) := by
      have : Epi (groupCohomology.δ hY n (n + 1) rfl ≫ shapiroMap S X.X₁ (n + 1)) := by
        rw [hcomm]
        infer_instance
      exact epi_of_epi (groupCohomology.δ hY n (n + 1) rfl) _
    have hmono : Mono (shapiroMap S A (n + 1)) := by
      rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective _).mp hδY x
      have h1 : groupCohomology.δ hX n (n + 1) rfl (shapiroMap S X.X₃ n y) = 0 := by
        rw [← ModuleCat.comp_apply, ← hcomm, ModuleCat.comp_apply]
        exact hx
      obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).mp
        (groupCohomology.mapShortComplex₃_exact hX (rfl : n + 1 = n + 1)) h1
      have hiso₂ := ih X.X₂
      have hiso₃ := ih X.X₃
      obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective _).mp
        (inferInstance : Epi (shapiroMap S X.X₂ n)) z
      have hy : groupCohomology.map (MonoidHom.id G) (Rep.coindMap S.subtype X.g) n z' = y := by
        apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (shapiroMap S X.X₃ n))
        rw [← ModuleCat.comp_apply, shapiroMap_naturality, ModuleCat.comp_apply]
        exact hz
      rw [← hy]
      exact congrArg (fun f => f z') (groupCohomology.mapShortComplex₃ hY
        (rfl : n + 1 = n + 1)).zero
    exact isIso_of_mono_of_epi _

/-- Shapiro's isomorphism `Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)` given by restriction to `S` and
evaluation at the identity. -/
def shapiroIso (A : Rep.{u} k S) (n : ℕ) :
    groupCohomology (Rep.coind S.subtype A) n ≅ groupCohomology A n :=
  @asIso _ _ _ _ (shapiroMap S A n) (isIso_shapiroMap S A n)

@[simp]
lemma shapiroIso_hom (A : Rep.{u} k S) (n : ℕ) :
    (shapiroIso S A n).hom = shapiroMap S A n :=
  rfl

end Langlands.Shapiro
