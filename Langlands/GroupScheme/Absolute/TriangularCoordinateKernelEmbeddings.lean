import Langlands.GroupScheme.Absolute.TriangularCoordinateQuotients
import Langlands.GroupScheme.AffineHomImageStatement
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer
import Langlands.GroupScheme.Rational.VectorGroupDimension

/-! # Closed additive embeddings of actual coordinate quotient kernels -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable {k : Type u} [Field k]

/-- A supplied actual fppf quotient by an additive coordinate's full kernel
is isomorphic to its closed additive image. The image-existence input is explicit. -/
theorem exists_closed_additive_embedding
    (himage : AffineHomImageStatement.{u})
    {K Q : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType K.X.hom] [IsAffineHom K.X.hom]
    (q : K ⟶ Q) [QuasiCompact q.hom.hom.left]
    (c : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι c)) q) :
    ∃ a : Q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
      IsClosedSubgroup a ∧ q ≫ a = c := by
  have : SmoothOfRelativeDimension 1
      (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
    VectorGroup.smoothOfRelativeDimension _ _
  have : Smooth (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
    SmoothOfRelativeDimension.smooth 1 _
  have : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom := by
    change IsAffineHom
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
    infer_instance
  obtain ⟨J, r, i, hft, haff, hi, hri, hr⟩ := himage k K _ c
  have := hft
  have := haff
  have : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom
  have : IsAffine J.X.left := isAffine_of_isAffineHom J.X.hom
  have : QuasiCompact r.hom.hom.left := inferInstance
  let e := FppfQuotientComparison.iso hq hr
  refine ⟨e.hom ≫ i, IsClosedSubgroup.iso_comp e hi, ?_⟩
  rw [← Category.assoc, FppfQuotientComparison.iso_fac, hri]

namespace QuotientTerm

variable {H K : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType K.X.hom] [IsAffineHom K.X.hom]
  {F E : SubgroupFunctor H} (A : QuotientTerm F) (B : QuotientTerm E)
  (hEF : E ≤ F) {i : K ⟶ H} (hi : F.IsRepresentedBy i)

/-- An exact full coordinate kernel on the larger subgroup gives a closed
embedding of the actual comparison kernel into the additive group. -/
theorem exists_kernelEmbedding
    (himage : AffineHomImageStatement.{u})
    (c : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (hc : SubgroupFunctor.range (kernelι c) = E.comap i) :
    ∃ a : kernel (comparison A B hEF) ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
      IsClosedSubgroup a ∧ kernelRestriction A B hEF hi ≫ a = c := by
  have hpb := (kernelRestriction_isPullback A B hEF hi).map
    (Over.forget (Spec (CommRingCat.of k)))
  have : QuasiCompact (kernelRestriction A B hEF hi).hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : QuasiCompact B.hom.hom.hom.left)
  have hr := kernelRestriction_isFppfQuotient A B hEF hi
  exact exists_closed_additive_embedding himage (kernelRestriction A B hEF hi) c
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.trans hc.symm⟩

end QuotientTerm

variable {H : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}

/-- The actual closed series inclusion represents its full subgroup functor. -/
theorem isRepresentedBy_seriesHom (ρ : MatrixRepresentation H (Fin N)) (t : ℕ) :
    (SubgroupFunctor.range (seriesHom ρ t)).IsRepresentedBy (seriesHom ρ t) := by
  have : IsClosedImmersion (seriesHom ρ t).hom.hom.left :=
    isClosedSubgroup_filtrationHom ρ _ _
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- Every enumerated successor has one additive coordinate; vacuous rows
use the zero homomorphism. -/
def seriesCoordinate (ρ : MatrixRepresentation H (Fin N)) (hN : 0 < N) (t : ℕ) :
    seriesScheme ρ t ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1 :=
  if h : t % N + t / N + 1 < N then
    filtrationCoordinate ρ (t / N) (t % N)
      ⟨t % N, Nat.mod_lt t hN⟩ ⟨t % N + t / N + 1, h⟩
  else 0

/-- The coordinate has precisely the next full subgroup as its kernel
inside the original group, including the repeated-term case. -/
theorem range_kernel_seriesCoordinate_all
    (ρ : MatrixRepresentation H (Fin N)) (hN : 0 < N) (t : ℕ) :
    SubgroupFunctor.range (kernelι (seriesCoordinate ρ hN t) ≫ seriesHom ρ t) =
      SubgroupFunctor.range (seriesHom ρ (t + 1)) := by
  by_cases h : t % N + t / N + 1 < N
  · have hc : seriesCoordinate ρ hN t =
        filtrationCoordinate ρ (t / N) (t % N)
          ⟨t % N, Nat.mod_lt t hN⟩ ⟨t % N + t / N + 1, h⟩ :=
      dite_eq_left h
    exact (congrArg (fun c : seriesScheme ρ t ⟶
      VectorGroup.groupScheme (CommRingCat.of k) 1 =>
        SubgroupFunctor.range (kernelι c ≫ seriesHom ρ t)) hc).trans
      (range_kernel_seriesCoordinate ρ hN t h)
  · have hc : seriesCoordinate ρ hN t = 0 := dite_eq_right h
    apply (congrArg (fun c : seriesScheme ρ t ⟶
      VectorGroup.groupScheme (CommRingCat.of k) 1 =>
        SubgroupFunctor.range (kernelι c ≫ seriesHom ρ t)) hc).trans
    rw [range_seriesHom_succ_of_out_of_range ρ hN t (Nat.le_of_not_gt h)]
    ext T x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
      exact SubgroupFunctor.mem_range.mpr
        ⟨y ≫ (kernelι (0 : seriesScheme ρ t ⟶
          VectorGroup.groupScheme (CommRingCat.of k) 1)).hom.hom,
          by simpa only [Grp.comp_hom_hom, Category.assoc] using hy⟩
    · intro hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
      have hy0 : y ∈ (SubgroupFunctor.range (kernelι
          (0 : seriesScheme ρ t ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1))).carrier T := by
        apply (mem_range_kernelι_iff _ y).mpr
        exact MonObj.comp_one y
      obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hy0
      exact SubgroupFunctor.mem_range.mpr ⟨z, by
        simpa only [Grp.comp_hom_hom, ← Category.assoc, hz] using hy⟩

/-- Internally to the current actual subgroup, the coordinate's full kernel
is the inverse image of the next term under the current inclusion. -/
theorem range_kernel_seriesCoordinate_comap
    (ρ : MatrixRepresentation H (Fin N)) (hN : 0 < N) (t : ℕ) :
    SubgroupFunctor.range (kernelι (seriesCoordinate ρ hN t)) =
      (SubgroupFunctor.range (seriesHom ρ (t + 1))).comap (seriesHom ρ t) := by
  have : Mono (seriesHom ρ t).hom.hom := (isRepresentedBy_seriesHom ρ t).1
  apply SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf
  apply (range_kernel_seriesCoordinate_all ρ hN t).trans
  ext T x
  exact ⟨fun hx => ⟨seriesHom_succ_le ρ hN t T hx, hx⟩, fun hx => hx.2⟩

variable [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]

/-- Both genuine-coordinate and repeated successors have actual comparison
kernels closed in the additive group, assuming generic image existence. -/
theorem exists_series_kernelEmbedding
    (himage : AffineHomImageStatement.{u})
    (ρ : MatrixRepresentation H (Fin N)) (hN : 0 < N) (t : ℕ)
    (A : QuotientTerm (SubgroupFunctor.range (seriesHom ρ t)))
    (B : QuotientTerm (SubgroupFunctor.range (seriesHom ρ (t + 1)))) :
    ∃ a : kernel (QuotientTerm.comparison A B (seriesHom_succ_le ρ hN t)) ⟶
        VectorGroup.groupScheme (CommRingCat.of k) 1,
      IsClosedSubgroup a ∧
        QuotientTerm.kernelRestriction A B (seriesHom_succ_le ρ hN t)
          (isRepresentedBy_seriesHom ρ t) ≫ a = seriesCoordinate ρ hN t := by
  have : LocallyOfFiniteType (seriesScheme ρ t).X.hom :=
    locallyOfFiniteType_filtrationScheme ρ _ _
  have : IsAffineHom (seriesScheme ρ t).X.hom :=
    isAffineHom_filtrationScheme ρ _ _
  exact QuotientTerm.exists_kernelEmbedding A B (seriesHom_succ_le ρ hN t)
    (isRepresentedBy_seriesHom ρ t) himage (seriesCoordinate ρ hN t)
    (range_kernel_seriesCoordinate_comap ρ hN t)

end Langlands.GroupScheme.TriangularLayer
