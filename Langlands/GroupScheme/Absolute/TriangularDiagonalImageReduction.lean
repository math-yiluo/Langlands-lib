import Langlands.GroupScheme.AffineHomImageStatement
import Langlands.GroupScheme.Torus.ClosedSubgroupPresentationStatement
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitTorus
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition

/-! # Reduction of triangular diagonal images to diagonalizable presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Postcomposition by a monomorphism preserves the full scheme-kernel range. -/
theorem range_kernelι_comp_mono {S : Scheme.{u}} {G Q R : GroupScheme S}
    (q : G ⟶ Q) (i : Q ⟶ R) [Mono i.hom.hom] :
    SubgroupFunctor.range (kernelι (q ≫ i)) = SubgroupFunctor.range (kernelι q) := by
  ext T x
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
  constructor
  · intro hx
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, hx, MonObj.one_comp]
  · intro hx
    rw [Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]

namespace DiagonalImageReduction

/-- Actual diagonalizable image data for a homomorphism, including its full-kernel
fppf quotient map. The character group is allowed to have torsion. -/
structure Presentation {k : Type u} [Field k]
    {H L : GroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ L) where
  characterGroup : Type u
  [addCommGroup : AddCommGroup characterGroup]
  [fg : AddGroup.FG characterGroup]
  inclusion : (Diagonalizable.groupScheme (CommRingCat.of k) characterGroup).toGrp ⟶ L
  projection : H ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) characterGroup).toGrp
  isClosedSubgroup : IsClosedSubgroup inclusion
  factorization : projection ≫ inclusion = f
  isFppfQuotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) projection

/-- Given the unrestricted affine-image and diagonalizable-subgroup statements,
a map to a split torus has a closed diagonalizable image presentation. Its
projection remains an fppf quotient by the full kernel of the original map. -/
theorem exists_diagonalizable_factorization
    (hImage : AffineHomImageStatement.{u})
    (hPresentation : Diagonalizable.ClosedSubgroupPresentationStatement.{u})
    (k : Type u) [Field k]
    (H L : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
    (hL : IsSplitTorus L) (f : H ⟶ L) :
    ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ)
      (d : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ L)
      (q : H ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
      IsClosedSubgroup d ∧ q ≫ d = f ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q := by
  classical
  have : Smooth L.X.hom := hL.smooth
  have : IsAffineHom L.X.hom := hL.isAffineHom
  obtain ⟨I, hI, ⟨eL⟩⟩ := hL
  let : Fintype I := Fintype.ofFinite I
  let eT := eL ≪≫ (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
  obtain ⟨J, q, i, hJft, hJaff, hi, hqi, hq⟩ := hImage k H L f
  obtain ⟨Λ, hΛ, hΛfg, ⟨e⟩⟩ := hPresentation k (I → ℤ) J (i ≫ eT.hom)
    (hi.comp_iso eT)
  refine ⟨Λ, hΛ, hΛfg, e.inv ≫ i, q ≫ e.hom, ?_, ?_, hq.comp_iso e⟩
  · exact hi.iso_comp e.symm
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hqi

/-- Choose actual diagonalizable image data from the two structural inputs. -/
def presentation
    (hImage : AffineHomImageStatement.{u})
    (hPresentation : Diagonalizable.ClosedSubgroupPresentationStatement.{u})
    (k : Type u) [Field k]
    (H L : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
    (hL : IsSplitTorus L) (f : H ⟶ L) : Presentation f :=
  Classical.choice (show Nonempty (Presentation f) from by
    obtain ⟨Λ, hΛ, hΛfg, d, q, hd, hqd, hq⟩ :=
      exists_diagonalizable_factorization hImage hPresentation k H L hL f
    exact ⟨{
      characterGroup := Λ
      addCommGroup := hΛ
      fg := hΛfg
      inclusion := d
      projection := q
      isClosedSubgroup := hd
      factorization := hqd
      isFppfQuotient := hq }⟩)

/-- The preceding image reduction applied to the actual diagonal projection of a
triangular homomorphism. The character group may have torsion. -/
theorem exists_triangular_diagonalizable_factorization
    (hImage : AffineHomImageStatement.{u})
    (hPresentation : Diagonalizable.ClosedSubgroupPresentationStatement.{u})
    (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
    (N : ℕ)
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))) :
    let L := GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))
    let f := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))
    ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ)
      (d : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ L)
      (q : H ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
      IsClosedSubgroup d ∧ q ≫ d = f ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q := by
  have he : Function.Injective (fun i : Fin N => -(i.val : ℤ)) := by
    intro i l h
    apply Fin.ext
    exact Int.ofNat_inj.mp (neg_injective h)
  exact exists_diagonalizable_factorization hImage hPresentation k H _
    ⟨ULift.{u} (Fin N), inferInstance,
      ⟨(GeneralLinear.diagonalTorusIso _ he (CommRingCat.of k)).symm⟩⟩ _

end DiagonalImageReduction
end Langlands.GroupScheme
