import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.Shimura.Unitary.DeligneNonSplitProof
import Langlands.Shimura.Unitary.DeligneReductiveStatement

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace Langlands.Shimura.DeligneTorus

open GroupScheme

/-- Every morphism from the spectrum of an algebraically closed field to `Spec ℝ` factors through
the complex point `complexBaseMap`. -/
theorem exists_factor_complexBaseMap (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℝ)) :
    ∃ c : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℂ), b = c ≫ complexBaseMap := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective b
  let : Algebra ℝ Ω := φ.hom.toAlgebra
  let ψ : ℂ →ₐ[ℝ] Ω := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
  rw [complexBaseMap, ← Spec.map_comp]
  congr 1
  ext x
  exact (ψ.commutes x).symm

/-- Every geometric base change of the real Deligne torus is a split torus. -/
theorem isSplitTorus_baseChange (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℝ)) :
    IsSplitTorus ((GroupScheme.baseChange b).obj groupScheme) := by
  obtain ⟨c, rfl⟩ := exists_factor_complexBaseMap Ω b
  exact IsSplitTorus.of_iso
    ((Functor.mapGrpNatIso (Over.pullbackComp c complexBaseMap)).app groupScheme ≪≫
      Functor.mapGrpCompIso.app groupScheme)
    (isSplitTorus_complexGroupScheme.baseChange c)

/-- The real Deligne torus is affine over `Spec ℝ`. -/
theorem isAffineHom_groupScheme : IsAffineHom groupScheme.X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap ℝ CoordinateRing)))
  infer_instance

/-- The real Deligne torus is connected: it is the image of its complex base change, which is a
split torus over `ℂ`. -/
theorem connectedSpace_groupScheme : ConnectedSpace groupScheme.X.left := by
  have h : ConnectedSpace (pullback (C := Scheme) groupScheme.X.hom complexBaseMap) :=
    isSplitTorus_complexGroupScheme.connectedSpace
  have : Surjective complexBaseMap := complexBaseMap_fpqc.1
  have hs : Surjective (pullback.fst groupScheme.X.hom complexBaseMap) := inferInstance
  exact Function.Surjective.connectedSpace (f := (pullback.fst groupScheme.X.hom complexBaseMap).base)
    hs.surj (pullback.fst groupScheme.X.hom complexBaseMap).base.hom.continuous

/-- The real Deligne torus is a connected reductive group over `ℝ`. -/
theorem isConnectedReductive_groupScheme : IsConnectedReductive groupScheme :=
  ⟨smooth_groupScheme, isAffineHom_groupScheme, connectedSpace_groupScheme,
    (isSplitTorus_baseChange (AlgebraicClosure ℝ) (toAlgebraicClosure ℝ)).hasTrivialUnipotentRadical⟩

/-- The real Deligne torus is a reductive group scheme over `Spec ℝ`. -/
theorem isReductive_groupScheme : IsReductive groupScheme :=
  ⟨smooth_groupScheme, isAffineHom_groupScheme, fun s =>
    (isSplitTorus_baseChange _ (geometricPoint _ s)).isPseudoReductive⟩

theorem reductiveStatement : ReductiveStatement :=
  ⟨isConnectedReductive_groupScheme, isReductive_groupScheme⟩

end Langlands.Shimura.DeligneTorus
