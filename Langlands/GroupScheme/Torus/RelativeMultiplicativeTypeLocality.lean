import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent

/-! # Fppf locality and commutativity of relative multiplicative-type groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S S' : Scheme.{u}} {H : GroupScheme S}

/-- Multiplicative type descends through every fppf covering family, by
composing the local diagonalizing covers. -/
theorem IsMultiplicativeType.of_fppfCover
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (hH : ∀ i, IsMultiplicativeType ((GroupScheme.baseChange (𝒰.f i)).obj H)) :
    IsMultiplicativeType H := by
  classical
  choose 𝒱 h𝒱 using hH
  refine ⟨𝒰.bind 𝒱, ?_⟩
  rintro ⟨i, j⟩
  exact IsDiagonalizable.of_iso
    (baseChangeCompIso (𝒰.f i) ((𝒱 i).f j) H) (h𝒱 i j)

/-- Multiplicative type can be checked on any fppf covering family. -/
theorem isMultiplicativeType_iff_fppfCover
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S) :
    IsMultiplicativeType H ↔
      ∀ i, IsMultiplicativeType ((GroupScheme.baseChange (𝒰.f i)).obj H) :=
  ⟨fun h i => h.baseChange (𝒰.f i), IsMultiplicativeType.of_fppfCover 𝒰⟩

/-- A single flat, surjective morphism locally of finite presentation
detects relative multiplicative type. -/
theorem IsMultiplicativeType.of_fppfBaseChange (b : S' ⟶ S)
    [Flat b] [Surjective b] [LocallyOfFinitePresentation b]
    (hH : IsMultiplicativeType ((GroupScheme.baseChange b).obj H)) :
    IsMultiplicativeType H := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers PUnit (fun _ => S') (fun _ => b)
      (fun s => by obtain ⟨s', hs'⟩ := b.surjective s; exact ⟨PUnit.unit, s', hs'⟩)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  exact IsMultiplicativeType.of_fppfCover 𝒰 (fun _ => hH)

/-- A diagonalizable group has a commutative group law. -/
theorem IsDiagonalizable.isCommMonObj (hH : IsDiagonalizable H) :
    IsCommMonObj H.X := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  have : IsCommMonObj (diagonalizable S M).X := by
    change IsCommMonObj
      ((CommGroupScheme.baseChange (Gm.toSpecZ S)).obj
        (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) M)).X
    infer_instance
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (isoPointsEquiv e T).injective
  rw [map_mul, map_mul, mul_comm]

/-- Commutativity descends along the actual fppf diagonalizing cover. -/
theorem IsMultiplicativeType.isCommMonObj (hH : IsMultiplicativeType H) :
    IsCommMonObj H.X := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  exact isCommMonObj_of_fppfCover 𝒰 fun i => (h𝒰 i).isCommMonObj

/-- The original multiplicative-type group with its commutative law made explicit. -/
def IsMultiplicativeType.commGroupScheme (hH : IsMultiplicativeType H) :
    CommGroupScheme S :=
  { H with comm := hH.isCommMonObj }

@[simp]
theorem IsMultiplicativeType.commGroupScheme_toGrp (hH : IsMultiplicativeType H) :
    hH.commGroupScheme.toGrp = H := rfl

/-- A group that becomes of relative multiplicative type on an fpqc cover
already has commutative multiplication. -/
theorem isCommMonObj_of_fpqcBaseChange (b : S' ⟶ S)
    [Flat b] [Surjective b] [QuasiCompact b]
    (hH : IsMultiplicativeType ((GroupScheme.baseChange b).obj H)) :
    IsCommMonObj H.X :=
  isCommMonObj_of_baseChange b H hH.isCommMonObj

end Langlands.GroupScheme.RelativeMultiplicativeType
