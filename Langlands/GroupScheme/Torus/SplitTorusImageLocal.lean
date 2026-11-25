import Langlands.CommutativeAlgebra.DiagonalGroupAlgebraImage
import Langlands.GroupScheme.HopfFiberCentrality
import Langlands.GroupScheme.Torus.DiagonalizableSourceCoordinates
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Local closed factorizations of maps from split tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.CommutativeAlgebra.DiagonalGroupAlgebraImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SplitTorusImageLocal

/-- A closed factorization with split torus image and flat surjective projection. -/
structure Factorization {S : Scheme.{u}} {T G : GroupScheme S} (f : T ⟶ G) where
  image : CommGroupScheme S
  projection : T ⟶ image.toGrp
  inclusion : image.toGrp ⟶ G
  isSplit : IsSplitTorus image.toGrp
  isClosed : IsClosedSubgroup inclusion
  flat : Flat projection.hom.hom.left
  surjective : Surjective projection.hom.hom.left
  fac : projection ≫ inclusion = f

private theorem isIso_left {S : Scheme.{u}} {G H : GroupScheme S} (e : G ≅ H) :
    IsIso e.hom.hom.hom.left :=
  inferInstanceAs (IsIso ((Over.forget S).mapIso ((Grp.forget _).mapIso e)).hom)

set_option maxHeartbeats 800000 in
/-- The image of a split torus in an affine group of locally finite type is a split
torus on a clopen basic open around each prime. -/
theorem exists_away_factorization {R : CommRingCat.{u}} {T G : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T)
    (f : T ⟶ G) (x : PrimeSpectrum R) :
    ∃ r : R, r ∉ x.asIdeal ∧ IsIdempotentElem r ∧
      Nonempty (Factorization ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).map f)) := by
  classical
  obtain ⟨I, hI, ⟨eI⟩⟩ := hT
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let M := I → ℤ
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let H := AffineCoordinates.hopfAlgebra G
  let C := Diagonalizable.hopfAlgebra R M
  let eT₀ : (Diagonalizable.groupScheme R M).toGrp ≅ T :=
    Diagonalizable.splitIso R (AddEquiv.refl M) ≪≫ eI.symm
  let eT := Diagonalizable.hopfSpecIso R M ≪≫ eT₀
  let eG := AffineCoordinates.hopfSpecIso G
  let φ : H ⟶ C := CompleteLocalDeformation.diagonalSourceCoordinateMap (eT₀.hom ≫ f)
  have hφ : (hopfSpec R).map φ.op = eT.hom ≫ f ≫ eG.inv := by
    rw [show φ = CompleteLocalDeformation.diagonalSourceCoordinateMap (eT₀.hom ≫ f) from rfl,
      CompleteLocalDeformation.diagonalSourceCoordinateMap_spec]
    simp only [eT, eG, Iso.trans_hom, Category.assoc]
  have hf : f = eT.inv ≫ (hopfSpec R).map φ.op ≫ eG.hom := by rw [hφ]; simp
  have : Algebra.FiniteType R H := AffineCoordinates.algebraFiniteType G
  obtain ⟨r, hr, hrid, L, q₀, hq, heq⟩ := exists_away_factor φ.hom x.asIdeal
  refine ⟨r, hr, hrid, ?_⟩
  let A := Localization.Away r
  let a := CommRingCat.of A
  let b := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let F := GroupScheme.baseChange b
  let HA := HopfCoordinates.scalarExtension R A H
  let CA := HopfCoordinates.scalarExtension R A C
  let c : CA ≅ Diagonalizable.hopfAlgebra a M :=
    (CommHopfAlgCat.ofIsoSelf CA).symm ≪≫
      CommHopfAlgCat.isoMk (scalarTensorBialgEquiv (R := R) (M := M) A)
  let q : HA ⟶ Diagonalizable.hopfAlgebra a L := CommHopfAlgCat.ofHom q₀
  let i : Diagonalizable.hopfAlgebra a L ⟶ Diagonalizable.hopfAlgebra a M :=
    CommHopfAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom A L.subtype)
  have hqi : HopfFiberCentrality.scalarExtensionMap A φ ≫ c.hom = q ≫ i :=
    CommHopfAlgCat.hom_ext heq.symm
  have hc : (hopfSpec a).map (HopfFiberCentrality.scalarExtensionMap A φ).op =
      (hopfSpec a).map c.inv.op ≫ (hopfSpec a).map i.op ≫ (hopfSpec a).map q.op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← hqi,
      Category.assoc, c.hom_inv_id, Category.comp_id]
  let D := Diagonalizable.groupScheme a L
  let eD := Diagonalizable.hopfSpecIso a L
  let e₁ : F.obj T ≅ (hopfSpec a).obj (op (Diagonalizable.hopfAlgebra a M)) :=
    (F.mapIso eT).symm ≪≫ HopfCoordinates.baseChangeSpecIso R A C ≪≫
      (hopfSpec a).mapIso c.symm.op
  let e₂ : (hopfSpec a).obj (op HA) ≅ F.obj G :=
    (HopfCoordinates.baseChangeSpecIso R A H).symm ≪≫ F.mapIso eG
  let p : F.obj T ⟶ D.toGrp := e₁.hom ≫ (hopfSpec a).map i.op ≫ eD.hom
  let j : D.toGrp ⟶ F.obj G := eD.inv ≫ (hopfSpec a).map q.op ≫ e₂.hom
  obtain ⟨n, v⟩ := Submodule.basisOfPid (Pi.basisFun ℤ I) L.toIntSubmodule
  let l : L ≃+ (ULift.{u} (Fin n) → ℤ) :=
    (v.equivFun.trans (LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift)).toAddEquiv
  have : Nontrivial A := by
    obtain ⟨y, _⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) := by
      rw [PrimeSpectrum.localization_away_comap_range A r]
      exact hr
    exact y.nontrivial
  have hflat : Flat ((hopfSpec a).map i.op).hom.hom.left ∧
      Surjective ((hopfSpec a).map i.op).hom.hom.left := by
    change Flat (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom A L.subtype))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom A L.subtype)))
    exact (flat_and_surjective_SpecMap_iff _).2
      (Diagonalizable.faithfullyFlat_mapDomainRingHom Subtype.val_injective A)
  have : Flat ((hopfSpec a).map i.op).hom.hom.left := hflat.1
  have : Surjective ((hopfSpec a).map i.op).hom.hom.left := hflat.2
  have : IsClosedImmersion ((hopfSpec a).map q.op).hom.hom.left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q₀.toAlgHom.toRingHom) hq
  have := isIso_left e₁
  have := isIso_left e₂
  have := isIso_left eD
  have := isIso_left eD.symm
  refine ⟨⟨D, p, j, Diagonalizable.isSplitTorus a l, ?_, ?_, ?_, ?_⟩⟩
  · change IsClosedImmersion (eD.inv.hom.hom.left ≫ ((hopfSpec a).map q.op).hom.hom.left ≫
      e₂.hom.hom.hom.left)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  · change Flat (e₁.hom.hom.hom.left ≫ ((hopfSpec a).map i.op).hom.hom.left ≫
      eD.hom.hom.hom.left)
    infer_instance
  · change Surjective (e₁.hom.hom.hom.left ≫ ((hopfSpec a).map i.op).hom.hom.left ≫
      eD.hom.hom.hom.left)
    infer_instance
  · change p ≫ j = F.map f
    conv_rhs => rw [hf, Functor.map_comp, Functor.map_comp]
    change p ≫ j = F.map eT.inv ≫
      (GroupScheme.baseChange b).map ((hopfSpec R).map φ.op) ≫ F.map eG.hom
    rw [HopfFiberCentrality.baseChange_hopfSpec A φ, hc]
    simp only [p, j, e₁, e₂, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      Iso.symm_hom, Iso.op_hom, Category.assoc, Iso.hom_inv_id_assoc]

end Langlands.GroupScheme.SplitTorusImageLocal
