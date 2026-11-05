import Langlands.Algebra.GroupLikeSubcoalgebra
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.ClosedSubgroupPresentationProof
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.AffineQuotientProof
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof
import Mathlib.RingTheory.Noetherian.Basic

/-! # Represented fppf quotients of groups of multiplicative type -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Diagonalizable

variable {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ]

/-- The additive character group of the monomial coalgebra is the original group. -/
def monomialGroupLikeAddEquiv : Λ ≃+ Additive (GroupLike k (AddMonoidAlgebra k Λ)) := by
  let f : Λ →+ Additive (GroupLike k (AddMonoidAlgebra k Λ)) :=
    AddMonoidHom.mk' (fun l => Additive.ofMul
      ⟨AddMonoidAlgebra.single l 1, AddMonoidAlgebra.isGroupLikeElem_single_one l⟩) (by
        intro a b
        apply Additive.toMul.injective
        apply GroupLike.val_injective
        simp only [toMul_ofMul, toMul_add, GroupLike.val_mul,
          AddMonoidAlgebra.single_mul_single, one_mul])
  exact AddEquiv.ofBijective f ⟨fun a b h =>
    AddMonoidAlgebra.single_left_injective one_ne_zero
      (congrArg (fun g => (Additive.toMul g).val) h), fun g => by
        obtain ⟨l, hl⟩ := AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one.mp
          (Additive.toMul g).isGroupLikeElem_val
        exact ⟨l, Additive.toMul.injective (GroupLike.val_injective hl)⟩⟩

/-- An injective bialgebra map embeds coordinate characters in the given character group. -/
def characterEmbedding {B : Type u} [CommRing B] [HopfAlgebra k B]
    (f : B →ₐc[k] AddMonoidAlgebra k Λ) : Additive (GroupLike k B) →+ Λ :=
  (monomialGroupLikeAddEquiv (k := k) (Λ := Λ)).symm.toAddMonoidHom.comp
    (AddMonoidHom.mk' (fun g => Additive.ofMul
      ⟨f (Additive.toMul g).val, (Additive.toMul g).isGroupLikeElem_val.map f⟩) (by
        intro a b
        apply Additive.toMul.injective
        apply GroupLike.val_injective
        simp only [toMul_ofMul, toMul_add, GroupLike.val_mul, map_mul]))

theorem characterEmbedding_injective {B : Type u} [CommRing B] [HopfAlgebra k B]
    (f : B →ₐc[k] AddMonoidAlgebra k Λ) (hf : Function.Injective f) :
    Function.Injective (characterEmbedding f) := by
  intro a b h
  apply Additive.toMul.injective
  apply GroupLike.val_injective
  apply hf
  exact congrArg (fun g => (Additive.toMul g).val)
    ((monomialGroupLikeAddEquiv (k := k) (Λ := Λ)).symm.injective h)

/-- An affine group with injective Hopf coordinates in a finite-type monomial
Hopf algebra is diagonalizable with a finitely generated full character group. -/
theorem presentation_of_injective [AddGroup.FG Λ]
    (Q : GroupScheme (Spec (CommRingCat.of k))) [IsAffine Q.X.left]
    (f : AffineCoordinates.hopfAlgebra Q →ₐc[k] AddMonoidAlgebra k Λ)
    (hf : Function.Injective f) :
    ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
      Nonempty (Q ≅ (groupScheme (CommRingCat.of k) Λ').toGrp) := by
  let B := AffineCoordinates.hopfAlgebra Q
  have hspan : Submodule.span k {b : B | IsGroupLikeElem k b} = ⊤ :=
    Langlands.AddMonoidAlgebra.span_isGroupLikeElem_of_injective f.toCoalgHom hf
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have : Module.Finite ℤ (Additive (GroupLike k B)) :=
    Module.Finite.of_injective (characterEmbedding f).toIntLinearMap
      (characterEmbedding_injective f hf)
  have hfg : AddGroup.FG (Additive (GroupLike k B)) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  let eRec : B ≃ₐc[k] AddMonoidAlgebra k (Additive (GroupLike k B)) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv k k (GroupLike k B))
  let eT := AffineCoordinates.isoOfBialgEquiv Q
    (hopfAlgebra (CommRingCat.of k) (Additive (GroupLike k B))) eRec
  exact ⟨Additive (GroupLike k B), inferInstance, hfg,
    ⟨eT.symm ≪≫ hopfSpecIso (CommRingCat.of k) (Additive (GroupLike k B))⟩⟩

/-- A faithfully flat quotient of an actual diagonalizable group is diagonalizable. -/
theorem quotientPresentation [AddGroup.FG Λ]
    {G Q : GroupScheme (Spec (CommRingCat.of k))} [IsAffine Q.X.left]
    (e : G ≅ (groupScheme (CommRingCat.of k) Λ).toGrp) (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] :
    ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
      Nonempty (Q ≅ (groupScheme (CommRingCat.of k) Λ').toGrp) := by
  let R := CommRingCat.of k
  let B := AffineCoordinates.hopfAlgebra Q
  let r := (hopfSpecIso R Λ).hom ≫ e.inv ≫ q ≫ (AffineCoordinates.hopfSpecIso Q).inv
  let φ : B ⟶ hopfAlgebra R Λ := (hopfSpec.fullyFaithful.preimage r).unop
  have hφ : (hopfSpec R).map φ.op = r := hopfSpec.fullyFaithful.map_preimage r
  let ψ := CommRingCat.ofHom φ.hom.toAlgHom.toRingHom
  have hψ : Spec.map ψ = r.hom.hom.left := congrArg (fun g => g.hom.hom.left) hφ
  have : IsIso (hopfSpecIso R Λ).hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso (hopfSpecIso R Λ).hom
  have : IsIso e.inv.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
  have : IsIso (AffineCoordinates.hopfSpecIso Q).inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso (AffineCoordinates.hopfSpecIso Q).inv
  have hflat : Flat (Spec.map ψ) := by
    rw [hψ]
    dsimp [r]
    infer_instance
  have hsurj : Surjective (Spec.map ψ) := by
    rw [hψ]
    dsimp [r]
    infer_instance
  have hinj : Function.Injective φ.hom :=
    ((flat_and_surjective_SpecMap_iff ψ).mp ⟨hflat, hsurj⟩).injective
  exact presentation_of_injective Q φ.hom hinj

end Diagonalizable

variable {k : Type u} [Field k] {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Geometry of a represented fppf target of a multiplicative-type group. -/
theorem IsMultiplicativeType.quotient_isAffineHom (hG : IsMultiplicativeType G)
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] : IsAffineHom Q.X.hom := by
  have : IsAffine G.X.left := hG.isAffine
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : LocallyOfFiniteType G.X.hom := hG.locallyOfFiniteType
  have hcomp : LocallyOfFiniteType (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : LocallyOfFiniteType Q.X.hom :=
    Langlands.AlgebraicGeometry.locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp
      _ _ _ q.hom.hom.left Q.X.hom inferInstance inferInstance inferInstance hcomp
  have : CompactSpace Q.X.left := Function.Surjective.compactSpace
    q.hom.hom.left.continuous q.hom.hom.left.surjective
  have : QuasiCompact Q.X.hom := inferInstance
  have : IsSeparated Q.X.hom := fieldSeparated k Q
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  exact affineGroupSchemeQuotient k G Q q

/-- Any represented fppf quotient of a finite-type multiplicative-type group
retains multiplicative type, including nonsmooth torsion data. -/
theorem IsMultiplicativeType.of_fppfHom (hG : IsMultiplicativeType G)
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] : IsMultiplicativeType Q := by
  have : IsAffineHom Q.X.hom := hG.quotient_isAffineHom q
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let qK := (GroupScheme.baseChange b).map q
  have : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom :=
    MorphismProperty.baseChange_obj (P := @IsAffineHom) b Q.X inferInstance
  have : IsAffine ((GroupScheme.baseChange b).obj Q).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj Q).X.hom
  have : Flat qK.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  have : Surjective qK.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  obtain ⟨Λ', hΛ', hfg', ⟨d⟩⟩ := Diagonalizable.quotientPresentation e qK
  exact ⟨K, hK, aK, Λ', hΛ', hfg', ⟨d⟩⟩

end Langlands.GroupScheme
