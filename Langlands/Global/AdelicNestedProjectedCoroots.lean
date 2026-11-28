import Langlands.Global.AdelicIntrinsicLeviChamber

/-! # Projected coroots at nested truncation levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open GroupScheme GroupScheme.RealTorusSpace ArthurRelative

variable {F : Type} [Field F]
  {G L : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} {iL : T.toGrp ⟶ L}
  [Mono i.hom.hom.left] [Mono iL.hom.hom.left]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hL : IsConnectedReductive L) (hiL : IsMaximalSplitTorus iL)
  (j : L ⟶ G) {ν : cocharacterLattice T}
  (D : RelativeRootReflectionData i) (DL : RelativeRootReflectionData iL)

include hG hi in
private theorem sameTorus_corootSubspace_eq (hc : iL ≫ j = i) {I : Set (characterLattice T)}
    (hI : I ⊆ simpleRelativeRoots i ν) (hIL : I ⊆ simpleRelativeRoots iL ν) :
    corootSubspace DL I = corootSubspace D I := by
  change Submodule.span ℝ (DL.realCorootsOf I) = Submodule.span ℝ (D.realCorootsOf I)
  congr 1
  ext x
  constructor
  · rintro ⟨β, hβ, rfl⟩
    let α : relativeRoots i := ⟨β.val, simpleRelativeRoots_subset_relativeRoots i ν (hI hβ)⟩
    exact ⟨α, hβ, (sameTorus_realCoroot_eq hG hi j hc D DL β α rfl).symm⟩
  · rintro ⟨α, hα, rfl⟩
    let β : relativeRoots iL := ⟨α.val, simpleRelativeRoots_subset_relativeRoots iL ν (hIL hα)⟩
    exact ⟨β, hα, sameTorus_realCoroot_eq hG hi j hc D DL β α rfl⟩

/-- With a common maximal split torus, the projections along a common set of simple coroots
are the same at the ambient and intrinsic levels. In particular a simple root shared by the
Levi and the ambient group contributes the same projected coroot in both cones. -/
def NestedProjectedCorootsStatement : Prop :=
  iL ≫ j = i → IsGenericCocharacter i ν → IsGenericCocharacter iL ν →
  ∀ I : Set (characterLattice T), I ⊆ simpleRelativeRoots i ν → I ⊆ simpleRelativeRoots iL ν →
    levelProjection hL hiL ν DL I = levelProjection hG hi ν D I ∧
    ∀ (β : relativeRoots iL) (α : relativeRoots i), β.val = α.val →
      levelProjection hL hiL ν DL I (DL.realCoroot β) =
        levelProjection hG hi ν D I (D.realCoroot α)

/-- Compare the kernels using equality of shared coroots, then use the common root
annihilator to identify the complementary projections. -/
theorem nestedProjectedCoroots : NestedProjectedCorootsStatement hG hi hL hiL j (ν := ν) D DL := by
  intro hc hν hνL I hI hIL
  have hspan := sameTorus_corootSubspace_eq hG hi j D DL hc hI hIL
  have hproj : levelProjection hL hiL ν DL I = levelProjection hG hi ν D I := by
    apply LinearMap.ext
    intro x
    let y := levelProjection hL hiL ν DL I x
    have hy : y ∈ aSpace T I := levelProjection_mem_rootAnnihilator hL hiL DL hνL hIL x
    have hz : x - y ∈ corootSubspace D I := by
      rw [← hspan]
      exact sub_levelProjection_mem_span hL hiL (ν := ν) DL I x
    change y = levelProjection hG hi ν D I x
    conv_rhs => rw [show x = y + (x - y) by abel]
    rw [map_add, ← levelProjection_eq_projectionOnto hG hi hν D hI y,
      Submodule.projectionOnto_apply_of_mem_left _ hy,
      ← levelProjection_eq_projectionOnto hG hi hν D hI (x - y),
      Submodule.projectionOnto_apply_of_mem_right _ hz]
    exact (add_zero y).symm
  exact ⟨hproj, fun β α he => by rw [hproj, sameTorus_realCoroot_eq hG hi j hc D DL β α he]⟩

omit [IsAffineHom L.X.hom] [Mono iL.hom.hom.left] in
/-- At nested ambient levels, projection to the larger Levi kills the coroot span of
both levels. -/
theorem levelProjection_nested (hν : IsGenericCocharacter i ν)
    {I J : Set (characterLattice T)} (hIJ : I ⊆ J) (hJ : J ⊆ simpleRelativeRoots i ν)
    (x : V T) :
    levelProjection hG hi ν D J (levelProjection hG hi ν D I x) =
      levelProjection hG hi ν D J x := by
  have hx : x - levelProjection hG hi ν D I x ∈ corootSubspace D J := by
    apply Submodule.span_mono (show D.realCorootsOf I ⊆ D.realCorootsOf J from by
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨α, hIJ hα, rfl⟩)
    exact sub_levelProjection_mem_span hG hi (ν := ν) D I x
  have hz : levelProjection hG hi ν D J (x - levelProjection hG hi ν D I x) = 0 := by
    rw [← levelProjection_eq_projectionOnto hG hi hν D hJ,
      Submodule.projectionOnto_apply_of_mem_right _ hx]
    rfl
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

omit [IsAffineHom L.X.hom] [Mono iL.hom.hom.left] in
/-- Outside coordinates of a coroot-span vector are unaffected by projection to the
level whose coroots lie in the discarded coordinates. -/
theorem weight_levelProjection_outside (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν) (ha : α ∉ J) (x : V T) :
    weight hG hi ν D (simpleRelativeRoots i ν) α (levelProjection hG hi ν D J x) =
      weight hG hi ν D (simpleRelativeRoots i ν) α x := by
  let w := weight hG hi ν D (simpleRelativeRoots i ν) α
  have hw : corootSubspace D J ≤ w.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    apply LinearMap.mem_ker.mpr
    change weight hG hi ν D (simpleRelativeRoots i ν) α (D.realCoroot β) = _
    rw [weight_coroot hG hi D hν subset_rfl hα β (hJ hβ),
      ite_eq_right (fun (he : α = β.val) => ha (he.symm ▸ hβ))]
  have hz := LinearMap.mem_ker.mp (hw (sub_levelProjection_mem_span hG hi (ν := ν) D J x))
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

end Langlands.Global.ArthurTruncation
