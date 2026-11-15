import Langlands.GroupScheme.Reductive.LocalSplitLocalGeneration

/-! # Matching point homomorphisms over local coefficient rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

section Field

variable (k : Type u) [Field k] [IsSepClosed k]

/-- A point and its right translate can simultaneously lie in an open
neighbourhood of the identity. -/
theorem exists_rationalPoint_mem_mul_mem
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (U : Set H.X.left) (hU : IsOpen U)
    (h0 : (1 : rationalPoints H).left (IsLocalRing.closedPoint k) ∈ U)
    (p : rationalPoints H) :
    ∃ q : rationalPoints H, q.left (IsLocalRing.closedPoint k) ∈ U ∧
      (q * p).left (IsLocalRing.closedPoint k) ∈ U := by
  let inv : H.X ⟶ H.X := (𝟙 H.X)⁻¹
  have hinv (q : rationalPoints H) : q ≫ inv = q⁻¹ := by
    simp only [inv, GrpObj.comp_inv, Category.comp_id]
  let V : Set H.X.left := U ∩ inv.left ⁻¹' U
  have hV : IsOpen V := hU.inter (hU.preimage inv.left.continuous)
  have hV0 : (1 : rationalPoints H).left (IsLocalRing.closedPoint k) ∈ V := by
    refine ⟨h0, ?_⟩
    change ((1 : rationalPoints H) ≫ inv).left (IsLocalRing.closedPoint k) ∈ U
    rw [hinv, inv_one]
    exact h0
  obtain ⟨q, hq, hqp⟩ :=
    exists_rationalPoint_mem_inv_mul_mem k H V hV 1 hV0 p
  refine ⟨q⁻¹, ?_, hqp.1⟩
  rw [← hinv]
  exact hq.2

end Field

section LocalTests

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [IsLocalRing A]
  {I : Type u} [Fintype I] {m n : ℕ}

/-- The coordinate cell lifts from the residue field of any local test ring. -/
theorem exists_cellPoint_lift_localResidue
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (x : Over.mk (Spec.algebraMap A (IsLocalRing.ResidueField A) ≫ s) ⟶
      cellObj R I m n) :
    ∃ y : Over.mk s ⟶ cellObj R I m n,
      Over.homMk (Spec.algebraMap A (IsLocalRing.ResidueField A)) rfl ≫ y = x := by
  let κ := IsLocalRing.ResidueField A
  let δ := Spec.algebraMap A κ
  let τ : Over.mk (δ ≫ s) ⟶ Over.mk s := Over.homMk δ rfl
  have hδ : IsClosedImmersion δ :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap A κ))
      IsLocalRing.residue_surjective
  have hs : Function.Surjective δ.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine δ).2
  let : IsLocalRing Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.isLocalRing
  let : Nontrivial Γ(Spec (CommRingCat.of κ), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of κ)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hl := IsLocalHom.of_surjective δ.appTop.hom hs
  exact exists_cellPoint_lift τ hs
    (IsLocalRing.surjective_units_map_of_local_ringHom δ.appTop.hom hs hl) x

/-- A map from a local test spectrum factors through an open immersion whenever
its closed point lies in that open. -/
theorem exists_lift_of_localPoint_closedPoint_mem
    {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X)
    [IsOpenImmersion f.left]
    {s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)}
    (x : Over.mk s ⟶ X)
    (hx : x.left (IsLocalRing.closedPoint A) ∈ Set.range f.left) :
    ∃ y : Over.mk s ⟶ Y, y ≫ f = x := by
  have hrange : Set.range x.left ⊆ Set.range f.left := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map x.left.continuous).mem_open
      (IsOpenImmersion.isOpen_range f.left) hx
  refine ⟨Over.homMk (IsOpenImmersion.lift f.left x.left hrange) ?_, ?_⟩
  · rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w x
  · ext1
    exact IsOpenImmersion.lift_fac _ _ _

variable [IsSepClosed (IsLocalRing.ResidueField A)]
  {G : GroupScheme (Spec (CommRingCat.of R))} {J : Type u}

/-- Every local-algebra point is a quotient of two points of the open
coordinate cell, with the inverse on the first factor. -/
theorem exists_inverse_cell_factors (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (fam : J → (Ga R ⟶ G))
    (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (g : Over.mk s ⟶ G.X) :
    ∃ x y : Over.mk s ⟶ cellObj R I m n,
      g = (x ≫ cellMap i fam neg pos)⁻¹ * (y ≫ cellMap i fam neg pos) := by
  let κ := IsLocalRing.ResidueField A
  let Ω := cellMap i fam neg pos
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let δ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of A) := Spec.algebraMap A κ
  let π := δ ≫ s
  let Gκ := (GroupScheme.baseChange π).obj G
  have : Smooth Gκ.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom π))
  have : IsAffineHom Gκ.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom π))
  have hκred : IsConnectedReductive Gκ :=
    fieldReductive_of_residueReductive G Set.univ
      (fun t _ => hG.isConnectedReductive_residueFiber t) π (Set.mem_univ _)
  have : ConnectedSpace Gκ.X.left := hκred.connectedSpace
  let e := baseChangeBasePointsEquiv π G
  let τ : Over.mk π ⟶ Over.mk s := Over.homMk δ rfl
  let r : (Over.mk s ⟶ G.X) →* (Over.mk π ⟶ G.X) :=
    { toFun := fun x => τ ≫ x
      map_one' := MonObj.comp_one τ
      map_mul' := fun x y => MonObj.comp_mul τ x y }
  have : IsLocalHom (algebraMap A κ) := inferInstanceAs (IsLocalHom (IsLocalRing.residue A))
  have hδ : δ (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint A :=
    IsLocalRing.comap_closedPoint (algebraMap A κ)
  have hr : ∀ x : Over.mk s ⟶ G.X,
      (r x).left (IsLocalRing.closedPoint κ) = x.left (IsLocalRing.closedPoint A) := by
    intro x
    change x.left (δ (IsLocalRing.closedPoint κ)) = _
    rw [hδ]
  have he : ∀ y : rationalPoints Gκ,
      (e y).left (IsLocalRing.closedPoint κ) =
        pullback.fst G.X.hom π (y.left (IsLocalRing.closedPoint κ)) := by
    intro y
    rw [baseChangeBasePointsEquiv_left]
    rfl
  let U : Set Gκ.X.left := (pullback.fst G.X.hom π) ⁻¹' Set.range Ω.left
  have hU : IsOpen U := (IsOpenImmersion.isOpen_range Ω.left).preimage
    (pullback.fst G.X.hom π).continuous
  let c0 : Over.mk s ⟶ cellObj R I m n := toUnit _ ≫ cellUnit R I m n
  have hc0 : c0 ≫ Ω = 1 := by
    dsimp only [c0, Ω]
    rw [Category.assoc, cellUnit_comp_cellMap, MonObj.comp_one]
  have h0' : (e.symm (r (c0 ≫ Ω))).left (IsLocalRing.closedPoint κ) ∈ U := by
    change pullback.fst G.X.hom π _ ∈ Set.range Ω.left
    rw [← he, MulEquiv.apply_symm_apply, hr]
    exact ⟨_, rfl⟩
  have h0 : (1 : rationalPoints Gκ).left (IsLocalRing.closedPoint κ) ∈ U := by
    simpa only [hc0, map_one] using h0'
  obtain ⟨q, hqU, hqpU⟩ :=
    exists_rationalPoint_mem_mul_mem κ Gκ U hU h0 (e.symm (r g))
  have hq : (e q).left (IsLocalRing.closedPoint κ) ∈ Set.range Ω.left := by
    rw [he]
    exact hqU
  have hqrange : Set.range (e q).left ⊆ Set.range Ω.left := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum κ) z (IsLocalRing.closedPoint κ)]
    exact hq
  let bq : Spec (CommRingCat.of κ) ⟶ (cellObj R I m n).left :=
    IsOpenImmersion.lift Ω.left (e q).left hqrange
  have hbq : bq ≫ (cellObj R I m n).hom = π := by
    rw [← Over.w Ω, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (e q)
  obtain ⟨x, hx⟩ := exists_cellPoint_lift_localResidue s
    (Over.homMk bq hbq : Over.mk π ⟶ cellObj R I m n)
  let h := x ≫ Ω
  have hrh : r h = e q := by
    change τ ≫ x ≫ Ω = e q
    rw [← Category.assoc, hx]
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac _ _ _
  have hk : (h * g).left (IsLocalRing.closedPoint A) ∈ Set.range Ω.left := by
    rw [← hr, map_mul, hrh, ← MulEquiv.apply_symm_apply e (r g), ← map_mul, he]
    exact hqpU
  obtain ⟨y, hy⟩ := exists_lift_of_localPoint_closedPoint_mem Ω (h * g) hk
  refine ⟨x, y, ?_⟩
  change g = h⁻¹ * (y ≫ Ω)
  rw [hy]
  group

variable {H : GroupScheme (Spec (CommRingCat.of R))}

/-- Agreement on the open coordinate cell determines a point homomorphism. -/
theorem pointHom_ext_of_cell (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (fam : J → (Ga R ⟶ G))
    (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (Ψ Φ : (Over.mk s ⟶ G.X) →* (Over.mk s ⟶ H.X))
    (hcell : ∀ x : Over.mk s ⟶ cellObj R I m n,
      Ψ (x ≫ cellMap i fam neg pos) = Φ (x ≫ cellMap i fam neg pos)) :
    Ψ = Φ := by
  ext g
  obtain ⟨x, y, hg⟩ := exists_inverse_cell_factors hG i fam neg pos s g
  rw [hg, map_mul, map_inv, map_mul, map_inv, hcell, hcell]

/-- A point homomorphism matching two open coordinate cells is bijective. -/
theorem pointHom_bijective_of_cell (hG : IsReductive G) (hH : IsReductive H)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (fam : J → (Ga R ⟶ G)) (fam' : J → (Ga R ⟶ H))
    (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left]
    [IsOpenImmersion (cellMap i' fam' neg pos).left]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (Ψ : (Over.mk s ⟶ G.X) →* (Over.mk s ⟶ H.X))
    (hcell : ∀ x : Over.mk s ⟶ cellObj R I m n,
      Ψ (x ≫ cellMap i fam neg pos) = x ≫ cellMap i' fam' neg pos) :
    Function.Bijective Ψ := by
  constructor
  · apply (injective_iff_map_eq_one Ψ).2
    intro g hg
    obtain ⟨x, y, hxy⟩ := exists_inverse_cell_factors hG i fam neg pos s g
    rw [hxy, map_mul, map_inv, hcell, hcell] at hg
    have h : x = y := (cancel_mono (cellMap i' fam' neg pos)).mp
      (inv_mul_eq_one.mp hg)
    rw [hxy, h, inv_mul_cancel]
  · intro h
    obtain ⟨x, y, hh⟩ := exists_inverse_cell_factors hH i' fam' neg pos s h
    refine ⟨(x ≫ cellMap i fam neg pos)⁻¹ * (y ≫ cellMap i fam neg pos), ?_⟩
    rw [map_mul, map_inv, hcell, hcell]
    exact hh.symm

/-- Matching the torus and root parametrizations forces bijectivity over
each local test ring with separably closed residue field. -/
theorem pointHom_bijective_of_matches (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
    {fam : J → (Ga R ⟶ G)} {fam' : J → (Ga R ⟶ H)}
    (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left]
    [IsOpenImmersion (cellMap i' fam' neg pos).left]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (Ψ : (Over.mk s ⟶ G.X) →* (Over.mk s ⟶ H.X))
    (hi : ∀ t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
      Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom)
    (hfam : ∀ α c, Ψ (rootPoint (fam α) _ c) = rootPoint (fam' α) _ c) :
    Function.Bijective Ψ :=
  pointHom_bijective_of_cell hG hH i i' fam fam' neg pos s Ψ
    (map_comp_cellMap Ψ hi hfam neg pos)

/-- There is at most one point homomorphism matching the supplied torus
and root parametrizations. -/
theorem pointHom_ext_of_matches (hG : IsReductive G)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
    {fam : J → (Ga R ⟶ G)} {fam' : J → (Ga R ⟶ H)}
    (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (Ψ Φ : (Over.mk s ⟶ G.X) →* (Over.mk s ⟶ H.X))
    (hΨi : ∀ t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
      Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom)
    (hΨfam : ∀ α c, Ψ (rootPoint (fam α) _ c) = rootPoint (fam' α) _ c)
    (hΦi : ∀ t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
      Φ (t ≫ i.hom.hom) = t ≫ i'.hom.hom)
    (hΦfam : ∀ α c, Φ (rootPoint (fam α) _ c) = rootPoint (fam' α) _ c) :
    Ψ = Φ := by
  apply pointHom_ext_of_cell hG i fam neg pos s Ψ Φ
  intro x
  rw [map_comp_cellMap Ψ hΨi hΨfam, map_comp_cellMap Φ hΦi hΦfam]

end LocalTests

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme

open LocalSplitCell

/-- A torus/root matching homomorphism on local test points is bijective
and uniquely determined, without a reducedness hypothesis. -/
def LocalSplitLocalPointHomStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [IsLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] (I : Type u) [Fintype I] (J : Type u)
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
      (fam : J → (Ga R ⟶ G)) (fam' : J → (Ga R ⟶ H))
      (m n : ℕ) (neg : Fin m → J) (pos : Fin n → J),
      IsOpenImmersion (cellMap i fam neg pos).left →
      IsOpenImmersion (cellMap i' fam' neg pos).left →
      ∀ (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
        (Ψ : (Over.mk s ⟶ G.X) →* (Over.mk s ⟶ H.X)),
        (∀ t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
          Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) →
        (∀ α c, Ψ (rootPoint (fam α) _ c) = rootPoint (fam' α) _ c) →
        Function.Bijective Ψ ∧
          ∀ Φ : (Over.mk s ⟶ G.X) →* (Over.mk s ⟶ H.X),
            (∀ t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
              Φ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) →
            (∀ α c, Φ (rootPoint (fam α) _ c) = rootPoint (fam' α) _ c) →
            Φ = Ψ

theorem localSplitLocalPointHom : LocalSplitLocalPointHomStatement.{u} := by
  intro R A _ _ _ _ I _ J G H hG hH i i' fam fam' m n neg pos hj hν s Ψ hi hfam
  let := hj
  let := hν
  refine ⟨pointHom_bijective_of_matches hG hH neg pos s Ψ hi hfam, ?_⟩
  intro Φ hΦi hΦfam
  exact pointHom_ext_of_matches hG neg pos s Φ Ψ hΦi hΦfam hi hfam

end Langlands.GroupScheme
