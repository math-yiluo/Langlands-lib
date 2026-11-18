import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceConstruction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-! # Covering families of étale affine charts

An algebraic space locally of finite type over `Spec K` has a family of étale affine charts,
indexed by the affine opens of an étale surjective atlas, such that for every affine test
point `y : Spec B → X` and every prime of `B`, some chart has the property that every affine
model of `Spec B ×_X Spec Aᵢ` has a prime over it.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K]

section Atlas

variable {U : Over (Spec (CommRingCat.of K))}

/-- The open chart of an affine open of an atlas, as a scheme over `Spec K`. -/
abbrev atlasChart (W : U.left.affineOpens) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (W.1.ι ≫ U.hom)

/-- The inclusion of an open chart in the atlas. -/
abbrev atlasChartι (W : U.left.affineOpens) : atlasChart W ⟶ U :=
  Over.homMk W.1.ι rfl

instance (W : U.left.affineOpens) : IsAffine (atlasChart W).left := W.2

/-- The coordinate algebra of the open chart of an affine open. -/
abbrev chartAlgebra (W : U.left.affineOpens) : Type u :=
  AffineCoordinateRing K (atlasChart W)

/-- The comparison of an open chart with the spectrum of its coordinate algebra. -/
abbrev chartIso (W : U.left.affineOpens) : atlasChart W ≅ ringTest K (chartAlgebra W) :=
  affineSchemeOverIso K (atlasChart W)

/-- The map `Spec Aᵂ → U` of an affine open of the atlas. -/
abbrev chartMap (W : U.left.affineOpens) : ringTest K (chartAlgebra W) ⟶ U :=
  (chartIso W).inv ≫ atlasChartι W

theorem etale_chartMap_left (W : U.left.affineOpens) : Etale (chartMap W).left := by
  rw [Over.comp_left]
  have : IsIso (chartIso W).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (chartIso W).inv))
  exact inferInstanceAs (Etale ((chartIso W).inv.left ≫ W.1.ι))

end Atlas

variable [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Every algebraic space locally of finite type over `Spec K` has a family of étale affine
charts covering all affine test points. -/
theorem nonempty_chartData {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX : LocallyOfFiniteTypeOverBase X) : Nonempty (ChartData X) := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX.exists_atlas
  let : ∀ W : U.left.affineOpens, LocallyOfFiniteType (atlasChart W).hom := fun W => by
    change LocallyOfFiniteType (W.1.ι ≫ U.hom)
    infer_instance
  let x : ∀ W : U.left.affineOpens, RingPoints K X (chartAlgebra W) := fun W =>
    uliftYonedaEquiv.{u + 1} ((schemeYoneda _).map (chartMap W) ≫ a)
  have hx : ∀ W, pointHom K (x W) = (schemeYoneda _).map (chartMap W) ≫ a := fun W =>
    uliftYonedaEquiv.{u + 1}.symm_apply_apply _
  refine ⟨{
    ι := U.left.affineOpens
    A := fun W => CommAlgCat.of K (chartAlgebra W)
    P := fun W => FinitePolynomialPresentation.ofFiniteType K (chartAlgebra W)
    x := x
    etale := fun W => by
      rw [hx]
      exact IsEtale.comp (isEtale_map _ (etale_chartMap_left W)) ha
    cover := ?_ }⟩
  intro B _ _ y 𝔭
  let hr := ha.representable
  let V := hr.pullback (pointHom K y)
  let φ : V ⟶ U := hr.fst' (pointHom K y)
  let ψ : V ⟶ ringTest K B := hr.snd (pointHom K y)
  have h : IsPullback ((schemeYoneda _).map φ) ((schemeYoneda _).map ψ) a (pointHom K y) :=
    hr.isPullback' (pointHom K y)
  have hψ : Surjective ψ.left := hs.projection (pointHom K y) _ ψ h
  obtain ⟨v, hv⟩ := ψ.left.surjective 𝔭
  obtain ⟨W', hvW⟩ : ∃ W' : U.left.affineOpens, φ.left v ∈ (W' : U.left.Opens) := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hvW, -⟩ :=
      U.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (φ.left v)) isOpen_univ
    exact ⟨⟨W, hW⟩, hvW⟩
  refine ⟨W', fun M => ?_⟩
  let O := φ.left ⁻¹ᵁ W'.1
  let V' : Over (Spec (CommRingCat.of K)) := Over.mk (O.ι ≫ V.hom)
  let ι' : V' ⟶ V := Over.homMk O.ι rfl
  let τ : V' ⟶ atlasChart W' := Over.homMk (φ.left ∣_ W'.1) (by
    change φ.left ∣_ W'.1 ≫ W'.1.ι ≫ U.hom = O.ι ≫ V.hom
    rw [morphismRestrict_ι_assoc, Over.w φ])
  have hτ : τ ≫ atlasChartι W' = ι' ≫ φ := by
    ext1
    exact morphismRestrict_ι φ.left W'.1
  have e : τ ≫ (chartIso W').hom ≫ chartMap W' = ι' ≫ φ := by
    change τ ≫ (chartIso W').hom ≫ (chartIso W').inv ≫ atlasChartι W' = ι' ≫ φ
    rw [Iso.hom_inv_id_assoc, hτ]
  have hcone : (schemeYoneda _).map (ι' ≫ ψ) ≫ pointHom K y =
      (schemeYoneda _).map (τ ≫ (chartIso W').hom) ≫ pointHom K (x W') := by
    rw [hx, ← Category.assoc, ← Functor.map_comp, Category.assoc, e]
    simp only [Functor.map_comp, Category.assoc, h.w]
  obtain ⟨χ, hχ⟩ := (schemeYoneda (Spec (CommRingCat.of K))).map_surjective
    (M.isPullback.lift _ _ hcone)
  have hχf : χ ≫ ringTestMap K M.f = ι' ≫ ψ := by
    apply (schemeYoneda (Spec (CommRingCat.of K))).map_injective
    rw [Functor.map_comp, hχ]
    exact M.isPullback.lift_fst _ _ hcone
  let v' : V'.left := ⟨v, hvW⟩
  refine ⟨χ.left v', ?_⟩
  have := congrArg (fun t : V' ⟶ ringTest K B => t.left v') hχf
  simp only [Over.comp_left] at this
  change (ringTestMap K M.f).left (χ.left v') = ψ.left v at this
  rw [← hv, ← this]
  rfl

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction
