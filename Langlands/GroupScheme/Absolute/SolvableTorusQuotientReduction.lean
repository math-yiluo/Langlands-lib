import Langlands.GroupScheme.Absolute.SolvableTorusQuotientStatement
import Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingProof
import Langlands.GroupScheme.Absolute.TriangularDiagonalKernelGeometryStatement
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitTorus
import Langlands.GroupScheme.Torus.SplitTorusQuotientFactor
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.HopfPrimitiveQuotient

/-! # Constructing the torus quotient of a solvable group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual split-torus fppf quotient obtained from a closed triangular embedding.
The kernel is specified on every test scheme; its smoothness, connectedness and
unipotence are not fields of this construction. -/
structure TriangularTorusQuotientData (H : GroupScheme (Spec (CommRingCat.of k))) where
  dimension : ℕ
  embedding : H ⟶ GeneralLinear.blockParabolicScheme (Fin dimension) (CommRingCat.of k)
    (fun i => -(i.val : ℤ))
  closed_embedding : IsClosedSubgroup embedding
  torus : GroupScheme (Spec (CommRingCat.of k))
  quotient : H ⟶ torus
  inclusion : torus ⟶ GeneralLinear.blockLeviScheme (Fin dimension) (CommRingCat.of k)
    (fun i => -(i.val : ℤ))
  split_torus : IsSplitTorus torus
  closed_inclusion : IsClosedSubgroup inclusion
  factorization : quotient ≫ inclusion = embedding ≫
    GeneralLinear.blockLimitHom (Fin dimension) (CommRingCat.of k) (fun i => -(i.val : ℤ))
  closed_kernel : IsClosedSubgroup (kernelι (embedding ≫
    GeneralLinear.blockLimitHom (Fin dimension) (CommRingCat.of k) (fun i => -(i.val : ℤ))))
  fppf_quotient : RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range (kernelι (embedding ≫
      GeneralLinear.blockLimitHom (Fin dimension) (CommRingCat.of k) (fun i => -(i.val : ℤ)))))
    quotient

/-- Choose a closed Lie–Kolchin embedding and factor its diagonal map through its
actual split-torus image. No kernel geometry or closed-subgroup unipotence is assumed. -/
def IsSolvableGroupScheme.triangularTorusQuotient
    [IsAlgClosed k] {H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hH : IsSolvableGroupScheme H) : TriangularTorusQuotientData H :=
  Classical.choice (by
    obtain ⟨N, j, hj⟩ := solvableTriangularEmbeddingStatement k H hH
    let weights : Fin N → ℤ := fun i => -(i.val : ℤ)
    have he : Function.Injective weights := by
      intro i l h
      apply Fin.ext
      exact Int.ofNat_inj.mp (neg_injective h)
    have hT : IsSplitTorus
        (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k) weights) :=
      ⟨ULift.{u} (Fin N), inferInstance,
        ⟨(GeneralLinear.diagonalTorusIso weights he (CommRingCat.of k)).symm⟩⟩
    let f := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) weights
    obtain ⟨D, q, m, hD, hm, hfac, hq⟩ := hT.exists_fppfQuotient_factor f
    have : IsAffineHom
        (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k) weights).X.hom :=
      hT.isAffineHom
    have hi : IsClosedSubgroup (kernelι f) := by
      change IsClosedImmersion (kernelι f).hom.hom.left
      infer_instance
    exact ⟨{
      dimension := N
      embedding := j
      closed_embedding := hj
      torus := D
      quotient := q
      inclusion := m
      split_torus := hD
      closed_inclusion := hm
      factorization := hfac
      closed_kernel := hi
      fppf_quotient := hq }⟩)

/-- The diagonal kernel embeds as a closed subgroup of the concrete unitriangular group.
Unipotence therefore follows from the explicit closed-subgroup inheritance premise. -/
theorem TriangularTorusQuotientData.isUnipotent_kernel
    {H : GroupScheme (Spec (CommRingCat.of k))} (Q : TriangularTorusQuotientData H)
    (hSub : UnipotentClosedSubgroupStatement.{u}) :
    IsUnipotent (kernel (Q.embedding ≫
      GeneralLinear.blockLimitHom (Fin Q.dimension) (CommRingCat.of k)
        (fun i => -(i.val : ℤ)))) := by
  let weights : Fin Q.dimension → ℤ := fun i => -(i.val : ℤ)
  let d := GeneralLinear.blockLimitHom (Fin Q.dimension) (CommRingCat.of k) weights
  let f := Q.embedding ≫ d
  let a : kernel f ⟶ kernel d :=
    pullback.lift (kernelι f ≫ Q.embedding) (pullback.snd f (kernelUnit _)) (by
      change (pullback.fst f (kernelUnit _) ≫ Q.embedding) ≫ d = _
      rw [Category.assoc, pullback.condition]
      rfl)
  have ha : a ≫ kernelι d = kernelι f ≫ Q.embedding := pullback.lift_fst _ _ _
  have : IsClosedImmersion Q.embedding.hom.hom.left := Q.closed_embedding
  have : IsClosedImmersion (kernelι f).hom.hom.left := Q.closed_kernel
  have ha_closed : IsClosedImmersion a.hom.hom.left := by
    have : IsClosedImmersion (a.hom.hom.left ≫ (kernelι d).hom.hom.left) := by
      change IsClosedImmersion ((a ≫ kernelι d).hom.hom.left)
      rw [ha]
      change IsClosedImmersion ((kernelι f).hom.hom.left ≫ Q.embedding.hom.hom.left)
      infer_instance
    exact IsClosedImmersion.of_comp a.hom.hom.left (kernelι d).hom.hom.left
  let e := GeneralLinear.blockUnipotentIsoKernel
    (Fin Q.dimension) (CommRingCat.of k) weights
  let w := a ≫ e.inv
  have hw : IsClosedSubgroup w := by
    have : IsClosedImmersion a.hom.hom.left := ha_closed
    have : IsIso e.inv.hom.hom.left :=
      ((Grp.forget (Over _)) ⋙ Over.forget _).map_isIso e.inv
    change IsClosedImmersion (a.hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  have : IsClosedImmersion (GeneralLinear.blockUnipotentHom
      (Fin Q.dimension) (CommRingCat.of k) weights).hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockUnipotentHom _ _ _
  have : IsAffineHom
      (GeneralLinear.groupScheme (Fin Q.dimension) (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme _ _
  have : IsAffineHom
      (GeneralLinear.blockUnipotentScheme (Fin Q.dimension) (CommRingCat.of k) weights).X.hom := by
    have h : IsAffineHom ((GeneralLinear.blockUnipotentHom
        (Fin Q.dimension) (CommRingCat.of k) weights).hom.hom.left ≫
      (GeneralLinear.groupScheme (Fin Q.dimension) (CommRingCat.of k)).X.hom) := inferInstance
    simpa only [Over.w] using h
  have : LocallyOfFiniteType
      (GeneralLinear.blockUnipotentScheme (Fin Q.dimension) (CommRingCat.of k) weights).X.hom := by
    have : Smooth
        (GeneralLinear.groupScheme (Fin Q.dimension) (CommRingCat.of k)).X.hom :=
      GeneralLinear.smoothStatement _ _
    have h : LocallyOfFiniteType ((GeneralLinear.blockUnipotentHom
        (Fin Q.dimension) (CommRingCat.of k) weights).hom.hom.left ≫
      (GeneralLinear.groupScheme (Fin Q.dimension) (CommRingCat.of k)).X.hom) := inferInstance
    simpa only [Over.w] using h
  exact hSub k _ (kernel f) w hw (unitriangularUnipotent k Q.dimension)

/-- The actual split-torus quotient construction reduces the exact solvable quotient
statement to smooth connected diagonal kernels and closed-subgroup unipotence. -/
theorem solvableTorusQuotient_of_kernel_prerequisites
    (hGeom : TriangularDiagonalKernelGeometryStatement.{u})
    (hSub : UnipotentClosedSubgroupStatement.{u}) :
    SolvableTorusQuotientStatement.{u} := by
  intro k _ _ H _ _ _ hH
  let Q := hH.triangularTorusQuotient
  obtain ⟨hs, hc⟩ := hGeom k H Q.dimension Q.embedding Q.closed_embedding
  let f := Q.embedding ≫ GeneralLinear.blockLimitHom
    (Fin Q.dimension) (CommRingCat.of k) (fun i => -(i.val : ℤ))
  exact ⟨kernel f, Q.torus, kernelι f, Q.quotient, Q.closed_kernel, hs, hc,
    Q.isUnipotent_kernel hSub, HopfPrimitive.isNormal_range_kernelι f,
    Q.fppf_quotient, Q.split_torus⟩

end Langlands.GroupScheme
