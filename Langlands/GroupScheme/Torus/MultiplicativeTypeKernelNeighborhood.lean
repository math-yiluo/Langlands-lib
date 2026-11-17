import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeMonomorphismSpreadingStatement
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.MatrixRepresentation.UnipotentQuotient
import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.KernelRepresentativeTransport

/-! # Identifying multiplicative-type kernels near a fibre using a supplied quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace MultiplicativeTypeKernelNeighborhood

variable {S : Scheme.{u}} {H G N Q : GroupScheme S}
    (f : H ⟶ G) (i : N ⟶ H) (q : H ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hkill : (i ≫ f).hom.hom = 1)

include hq hkill

/-- Killing a supplied subgroup kills the full kernel of a quotient by it. -/
theorem kernel_comp_eq_zero : kernelι q ≫ f = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ f.hom.hom = 1
  have hx : (kernelι q).hom.hom ∈
      (SubgroupFunctor.range i).carrier (kernel q).X := by
    rw [← hq.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hx, Category.assoc]
  change x ≫ (i ≫ f).hom.hom = 1
  rw [hkill, MonObj.comp_one]

variable [QuasiCompact q.hom.hom.left]

/-- Descend an actual homomorphism killing the subgroup of a supplied quotient. -/
def factor : Q ⟶ G :=
  letI := hq.1
  letI := hq.2.1
  FpqcHomDescent.hom q f (kernel_comp_eq_zero f i q hq hkill)

@[reassoc]
theorem fac : q ≫ factor f i q hq hkill = f := by
  have := hq.1
  have := hq.2.1
  exact FpqcHomDescent.fac q f (kernel_comp_eq_zero f i q hq hkill)

/-- If the supplied subgroup is the full kernel on one fibre, then the
factor through its affine quotient is monic on that fibre. -/
theorem mono_factor_fibre [IsAffineHom q.hom.hom.left] (s : S)
    (hs :
      SubgroupFunctor.range
          (kernelι ((baseChange (S.fromSpecResidueField s)).map f)) =
        SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i)) :
    Mono ((baseChange (S.fromSpecResidueField s)).map
      (factor f i q hq hkill)).hom.hom := by
  let b := S.fromSpecResidueField s
  let B := baseChange b
  have hqb := hq.baseChange b
  have : Flat (B.map q).hom.hom.left := hqb.1
  have : Surjective (B.map q).hom.hom.left := hqb.2.1
  have : IsAffineHom (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsAffineHom) b q.hom.hom inferInstance
  apply FpqcHomDescent.mono_of_kernel_range_le
    (B.map q) (B.map f) (B.map (factor f i q hq hkill))
  · rw [← B.map_comp, fac]
  · rw [hqb.2.2.2, ← SubgroupFunctor.range_baseChangeHom, hs]

/-- Monomorphism spreading identifies the actual kernel with the supplied
multiplicative-type subgroup on a neighborhood of the chosen fibre.
The spreading theorem is an explicit premise. -/
theorem exists_neighborhood
    (hmono : MultiplicativeTypeMonomorphismSpreadingStatement.{u})
    [IsAffineHom q.hom.hom.left] [Mono i.hom.hom]
    (hN : RelativeMultiplicativeType.IsMultiplicativeType N)
    (hQ : RelativeMultiplicativeType.IsMultiplicativeType Q)
    (hG : IsSeparated G.X.hom)
    (hfin : IsLocallyNoetherian S ∨ LocallyOfFinitePresentation G.X.hom)
    (s : S)
    (hs :
      SubgroupFunctor.range
          (kernelι ((baseChange (S.fromSpecResidueField s)).map f)) =
        SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i)) :
    ∃ U : S.Opens, s ∈ U ∧
      SubgroupFunctor.range (kernelι ((baseChange U.ι).map f)) =
        SubgroupFunctor.range ((baseChange U.ι).map i) ∧
      RelativeMultiplicativeType.IsMultiplicativeType
        (kernel ((baseChange U.ι).map f)) := by
  let v := factor f i q hq hkill
  have hsv : Mono ((baseChange (S.fromSpecResidueField s)).map v).hom.hom :=
    mono_factor_fibre f i q hq hkill s hs
  obtain ⟨U, hsU, hUv⟩ := (hmono S Q G hQ hfin v).1 hG s hsv
  let B := baseChange U.ι
  have hUq := hq.baseChange U.ι
  have : Mono (B.map v).hom.hom := hUv
  have : Mono (B.map i).hom.hom := by
    change Mono ((CategoryTheory.Over.pullback U.ι).map i.hom.hom)
    infer_instance
  have hfac : B.map q ≫ B.map v = B.map f := by
    rw [← B.map_comp]
    exact congrArg B.map (fac f i q hq hkill)
  have hker : SubgroupFunctor.range (kernelι (B.map f)) =
      SubgroupFunctor.range (B.map i) := by
    rw [← hfac, range_kernelι_comp_mono, hUq.2.2.2,
      SubgroupFunctor.range_baseChangeHom]
  exact ⟨U, hsU, hker,
    RelativeMultiplicativeType.IsMultiplicativeType.of_iso
      (KernelRepresentative.iso (B.map f) (B.map i) hker) (hN.baseChange U.ι)⟩

/-- Choose the actual neighborhood supplied by the conditional kernel-identification
theorem. No monomorphism-spreading proof is asserted here. -/
def neighborhood
    (hmono : MultiplicativeTypeMonomorphismSpreadingStatement.{u})
    [IsAffineHom q.hom.hom.left] [Mono i.hom.hom]
    (hN : RelativeMultiplicativeType.IsMultiplicativeType N)
    (hQ : RelativeMultiplicativeType.IsMultiplicativeType Q)
    (hG : IsSeparated G.X.hom)
    (hfin : IsLocallyNoetherian S ∨ LocallyOfFinitePresentation G.X.hom)
    (s : S)
    (hs :
      SubgroupFunctor.range
          (kernelι ((baseChange (S.fromSpecResidueField s)).map f)) =
        SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i)) :
    S.Opens :=
  (exists_neighborhood f i q hq hkill hmono hN hQ hG hfin s hs).choose

end MultiplicativeTypeKernelNeighborhood

end Langlands.GroupScheme
