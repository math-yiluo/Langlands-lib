import Langlands.Algebra.CentralDiagonalizableExtensionHopf
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.Lattice

/-! # Central extensions of split tori by diagonalizable groups are diagonalizable

Let `E` be an affine group scheme over a field `K`, `z : Z ⟶ E` a central closed subgroup and
`p : E ⟶ T` an fppf quotient map with kernel `Z`. If `Z ≅ D_K(Λ)` with `Λ` finitely generated
and `T` is a split torus, then `E ≅ D_K(Λ')` with `Λ'` finitely generated. The proof transports
the data to the coordinate Hopf algebra of `E`, where `CentralDiagonalizableExtensionHopf` shows
that the group-like elements span and form a finitely generated group. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralExtensionHopfSpec

open HopfSpecPoints RelativeRoot

variable {K : Type u} [Field K] {I Λ : Type u} [AddCommGroup Λ]
  {A : CommHopfAlgCat.{u} (CommRingCat.of K)}

/-- The Hopf algebra data of a central extension of a split torus by a diagonalizable group: if
`Spec π` is a central closed subgroup of `Spec A` and `Spec φ` is an fppf quotient map with
kernel `Spec π`, then `φ` and `π` satisfy
`CentralDiagonalizableExtensionHopf.IsCentralExtension`. -/
theorem isCentralExtension_diagonalizable
    (φ : Diagonalizable.hopfAlgebra (CommRingCat.of K) (I → ℤ) ⟶ A)
    (π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of K) Λ)
    (hz : IsClosedSubgroup ((hopfSpec (CommRingCat.of K)).map π.op))
    (hc : IsCentral ((hopfSpec (CommRingCat.of K)).map π.op))
    (hq : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec (CommRingCat.of K)).map π.op))
      ((hopfSpec (CommRingCat.of K)).map φ.op)) :
    CentralDiagonalizableExtensionHopf.IsCentralExtension (K := K) (A := A) φ.hom π.hom where
  injective := (faithfullyFlat_of_isFppfQuotient φ hq).injective
  surjective := surjective_of_isClosedSubgroup π hz
  comp_eq b := by
    have h := congrArg (fun f => f b) (comp_eq_of_range_kernelι φ π hq.2.2.2)
    simpa using h
  isCentral := rTensor_comul_eq_of_isCentral π hc
  invariants a ha := by
    have : IsClosedImmersion ((hopfSpec (CommRingCat.of K)).map π.op).hom.hom.left := hz
    refine exists_eq_of_lTensor_comul_eq φ π (Over.mono_of_mono_left _) hq a ?_
    rw [GroupAlgebraCoaction.mem_grade_iff, GroupAlgebraCoaction.coaction_apply] at ha
    rw [← (AddMonoidAlgebra.scalarTensorEquiv K A).symm_apply_apply
      ((π.hom : A →ₗ[K] AddMonoidAlgebra K Λ).lTensor A (comul a)), ha,
      AddMonoidAlgebra.scalarTensorEquiv_symm_single, ← AddMonoidAlgebra.one_def]

/-- A central extension of a split torus by a diagonalizable group is diagonalizable, for an
affine group scheme over a field: if `z : Z ⟶ E` is a central closed subgroup, `p : E ⟶ T` is an
fppf quotient map with kernel `Z`, `Z ≅ D_K(Λ)` with `Λ` finitely generated and `T ≅ 𝔾_m^I`,
then `E ≅ D_K(Λ')` for a finitely generated `Λ'`. -/
theorem exists_iso_diagonalizable_of_split {E Z T : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine E.X.left] [Finite I] [AddGroup.FG Λ]
    (eZ0 : Z ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (eT0 : T ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ T) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) :
    ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
      Nonempty (E ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ').toGrp) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let R := CommRingCat.of K
  let A := AffineCoordinates.hopfAlgebra E
  let eE := AffineCoordinates.hopfSpecIso E
  let eZ : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R Λ)) ≅ Z :=
    Diagonalizable.hopfSpecIso R Λ ≪≫ eZ0.symm
  let eT : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R (I → ℤ))) ≅ T :=
    Diagonalizable.hopfSpecIso R (I → ℤ) ≪≫
      Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ eT0.symm
  let π : A ⟶ Diagonalizable.hopfAlgebra R Λ :=
    (hopfSpec.fullyFaithful.preimage (eZ.hom ≫ z ≫ eE.symm.hom)).unop
  let φ : Diagonalizable.hopfAlgebra R (I → ℤ) ⟶ A :=
    (hopfSpec.fullyFaithful.preimage (eE.symm.inv ≫ p ≫ eT.symm.hom)).unop
  have hπ : (hopfSpec R).map π.op = eZ.hom ≫ z ≫ eE.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hφ : (hopfSpec R).map φ.op = eE.symm.inv ≫ p ≫ eT.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hz' : IsClosedSubgroup ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eZ (hz.comp_iso eE.symm)
  have hc' : IsCentral ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact (hc.comp_iso eE.symm).comp eZ.hom
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec R).map π.op))
      ((hopfSpec R).map φ.op) := by
    rw [hπ, hφ, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_comp_iso,
      ← Category.assoc]
    exact (hq.comapIso eE.symm).comp_iso eT.symm
  have h := isCentralExtension_diagonalizable φ π hz' hc' hq'
  have hspan := CentralDiagonalizableExtensionHopf.span_isGroupLikeElem h
  let eRec : A ≃ₐc[K] AddMonoidAlgebra K (Additive (GroupLike K A)) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv K K (GroupLike K A))
  let e1 := AffineCoordinates.isoOfBialgEquiv E
    (Diagonalizable.hopfAlgebra R (Additive (GroupLike K A))) eRec
  exact ⟨Additive (GroupLike K A), inferInstance, CentralDiagonalizableExtensionHopf.addGroupFG h,
    ⟨e1.symm ≪≫ Diagonalizable.hopfSpecIso R (Additive (GroupLike K A))⟩⟩

end Langlands.GroupScheme.CentralExtensionHopfSpec

namespace Langlands.GroupScheme.RelativeRoot.IsFppfQuotient

open CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme.{u}} {H G K : GroupScheme S} (i : H ⟶ G) [Mono i.hom.hom]
    {p : G ⟶ K} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)

include i hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An fppf quotient map whose represented kernel is affine is an affine morphism. The
quotient pullback `G ×_K G ≅ G × H` has affine first projection; affineness descends along the
fppf cover `p`. (The same argument appears in Worker 312's helper module
`MultiplicativeTypeExtensionHelpers`.) -/
theorem isAffineHom_of_isAffineHom_kernel [IsAffineHom H.X.hom] :
    IsAffineHom p.hom.hom.left := by
  have hpb := (QuotientCell.multiplication_isPullback i (𝟙 G.X) p.hom.hom
    (hq.fibers_iff ⟨inferInstance, rfl⟩)).map (Over.forget S)
  change IsPullback (QuotientCell.multiplication i (𝟙 G.X)).left
    (fst G.X H.X).left p.hom.hom.left ((𝟙 G.X) ≫ p.hom.hom).left at hpb
  simp only [Category.id_comp] at hpb
  have hsource : IsAffineHom (fst G.X H.X).left := by
    change IsAffineHom (Limits.pullback.fst G.X.hom H.X.hom)
    exact MorphismProperty.pullback_fst G.X.hom H.X.hom
      (inferInstanceAs (IsAffineHom H.X.hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    hpb.flip ⟨⟨hq.2.1, hq.1⟩, hq.2.2.1⟩ hsource

end Langlands.GroupScheme.RelativeRoot.IsFppfQuotient

namespace Langlands.GroupScheme.RelativeRoot.IsFppfQuotient

/-- Over a field, a monomorphism `i` whose range is the kernel of an fppf quotient map is a
closed subgroup: it is the actual kernel, which is closed because the quotient is separated. -/
theorem isClosedSubgroup_of_field {k : Type u} [Field k]
    {H G K : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) [Mono i.hom.hom]
    {p : G ⟶ K} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p) :
    IsClosedSubgroup i := by
  have hz : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  have : IsSeparated K.X.hom := fieldSeparated k K
  have hiso : IsIso (hq.kernelIso hz).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Grp.forget _).map (hq.kernelIso hz).hom)))
  rw [← hq.kernelIso_hom_comp hz]
  change IsClosedImmersion ((hq.kernelIso hz).hom.hom.hom.left ≫ (kernelι p).hom.hom.left)
  infer_instance

end Langlands.GroupScheme.RelativeRoot.IsFppfQuotient

namespace Langlands.GroupScheme

open RelativeRoot

variable {k : Type u} [Field k]

/-- **Central extensions of split tori by diagonalizable groups over a field.** Let
`i : H ⟶ G` be a monomorphism of group schemes over a field `k` and `p : G ⟶ K` an fppf
quotient map with kernel the range of `i`. If `i` is central, `H ≅ D_k(Λ)` with `Λ` finitely
generated and `K` is a split torus, then `G ≅ D_k(Λ')` for a finitely generated `Λ'`. -/
theorem exists_iso_diagonalizable_of_isCentral
    {H G K : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) (p : G ⟶ K)
    [Mono i.hom.hom] (hq : IsFppfQuotient (SubgroupFunctor.range i) p) (hc : IsCentral i)
    (hH : ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp))
    (hK : IsSplitTorus K) :
    ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
      Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp) := by
  obtain ⟨Λ, _, _, ⟨eH⟩⟩ := hH
  have : IsAffineHom K.X.hom := hK.isAffineHom
  obtain ⟨I, _, ⟨eK⟩⟩ := hK
  have : IsAffineHom H.X.hom :=
    isAffineHom_of_over_iso ((Grp.forget _).mapIso eH)
      (Diagonalizable.isAffineHom (CommRingCat.of k) Λ)
  have : IsAffineHom p.hom.hom.left := hq.isAffineHom_of_isAffineHom_kernel i
  have : IsAffineHom G.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact CentralExtensionHopfSpec.exists_iso_diagonalizable_of_split eH eK i
    (IsFppfQuotient.isClosedSubgroup_of_field i hq) hc p hq

/-- The variant of `exists_iso_diagonalizable_of_isCentral` for a commutative `G`. -/
theorem exists_iso_diagonalizable_of_isCommMonObj
    {H G K : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) (p : G ⟶ K)
    [Mono i.hom.hom] (hq : IsFppfQuotient (SubgroupFunctor.range i) p) [IsCommMonObj G.X]
    (hH : ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp))
    (hK : IsSplitTorus K) :
    ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
      Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp) :=
  exists_iso_diagonalizable_of_isCentral i p hq (fun _ _ _ _ _ => Commute.all _ _) hH hK

/-- A group scheme isomorphic to `D_k(Λ)` with `Λ` finitely generated is of multiplicative
type: the trivial extension `k / k` splits it. -/
theorem isMultiplicativeType_of_iso_diagonalizable {H : GroupScheme (Spec (CommRingCat.of k))}
    {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
    (e : H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp) :
    IsMultiplicativeType H :=
  IsMultiplicativeType.of_iso e ⟨k, inferInstance, inferInstance, Λ, inferInstance, inferInstance,
    ⟨Diagonalizable.baseChangeIso _ Λ⟩⟩

/-- **Part 2 of SGA 3 IX 8.2 over a field, from part 1.** Let `i : H ⟶ G` be a monomorphism
and `p : G ⟶ K` an fppf quotient map with kernel the range of `i`, with `H ≅ D_k(Λ)` for a
finitely generated `Λ` and `K` a split torus. Assume part 1 for this extension: if `H` and `K`
are of multiplicative type and `G` is commutative or `K` is connected, then `G` is of
multiplicative type. Then `G ≅ D_k(Λ')` for a finitely generated `Λ'`. -/
theorem exists_iso_diagonalizable_of_part_one
    {H G K : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) (p : G ⟶ K)
    [Mono i.hom.hom] (hq : IsFppfQuotient (SubgroupFunctor.range i) p)
    (h1 : IsMultiplicativeType H → IsMultiplicativeType K →
      (IsCommMonObj G.X ∨ ConnectedSpace K.X.left) → IsMultiplicativeType G)
    (hH : ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp))
    (hK : IsSplitTorus K) :
    ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
      Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp) := by
  have hHm : IsMultiplicativeType H := by
    obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
    exact isMultiplicativeType_of_iso_diagonalizable e
  have hG : IsMultiplicativeType G :=
    h1 hHm hK.isTorus.isMultiplicativeType (Or.inr hK.connectedSpace)
  have : IsCommMonObj G.X := hG.isCommMonObj
  exact exists_iso_diagonalizable_of_isCommMonObj i p hq hH hK

end Langlands.GroupScheme
