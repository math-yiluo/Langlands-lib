import Langlands.Algebra.ConnectedExtensionHopf
import Langlands.GroupScheme.Torus.CentralDiagonalizableExtensionSplit
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaProof
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent

/-! # Extensions of multiplicative-type groups with connected quotient are commutative

Let `k` be a field, `i : H ⟶ G` a monomorphism and `p : G ⟶ K` an fppf quotient map with kernel
the range of `i`. If `H` and `K` are of multiplicative type and `K` is connected, then `G` is
commutative. The proof base changes to a field over which `H` and `K` are diagonalizable,
translates the extension into the coordinate Hopf algebra of `G`, and applies
`ConnectedExtensionHopf.isCocomm`. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

/-! ### The diagonalizable case -/

namespace CentralExtensionHopfSpec

variable {K : Type u} [Field K] {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
  {A : CommHopfAlgCat.{u} (CommRingCat.of K)}

/-- The Hopf algebra data of an extension of a diagonalizable group by a diagonalizable group:
if `Spec π` is a closed subgroup of `Spec A` and `Spec φ` is an fppf quotient map with kernel
`Spec π`, then `φ` and `π` satisfy `ConnectedExtensionHopf.IsExtension`. -/
theorem isExtension_diagonalizable
    (φ : Diagonalizable.hopfAlgebra (CommRingCat.of K) Λ' ⟶ A)
    (π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of K) Λ)
    (hz : IsClosedSubgroup ((hopfSpec (CommRingCat.of K)).map π.op))
    (hq : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec (CommRingCat.of K)).map π.op))
      ((hopfSpec (CommRingCat.of K)).map φ.op)) :
    ConnectedExtensionHopf.IsExtension (K := K) (A := A) φ.hom π.hom where
  injective := (faithfullyFlat_of_isFppfQuotient φ hq).injective
  surjective := surjective_of_isClosedSubgroup π hz
  comp_eq b := by
    have h := congrArg (fun f => f b) (comp_eq_of_range_kernelι φ π hq.2.2.2)
    simpa using h
  invariants a ha := by
    have : IsClosedImmersion ((hopfSpec (CommRingCat.of K)).map π.op).hom.hom.left := hz
    refine exists_eq_of_lTensor_comul_eq φ π (Over.mono_of_mono_left _) hq a ?_
    rw [GroupAlgebraCoaction.mem_grade_iff, GroupAlgebraCoaction.coaction_apply] at ha
    rw [← (AddMonoidAlgebra.scalarTensorEquiv K A).symm_apply_apply
      ((π.hom : A →ₗ[K] AddMonoidAlgebra K Λ).lTensor A (Coalgebra.comul a)), ha,
      AddMonoidAlgebra.scalarTensorEquiv_symm_single, ← AddMonoidAlgebra.one_def]

/-- An extension of a connected diagonalizable group by a diagonalizable group is commutative,
for an affine group scheme over a field: if `z : Z ⟶ E` is a closed subgroup, `p : E ⟶ T` is an
fppf quotient map with kernel `Z`, `Z ≅ D_K(Λ)`, `T ≅ D_K(Λ')` and `T` is connected, then `E` is
commutative. -/
theorem isCommMonObj_of_diagonalizable_connected {E Z T : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine E.X.left]
    (eZ0 : Z ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (eT0 : T ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ').toGrp)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (p : E ⟶ T)
    (hq : IsFppfQuotient (SubgroupFunctor.range z) p) [ConnectedSpace T.X.left] :
    IsCommMonObj E.X := by
  classical
  let R := CommRingCat.of K
  let A := AffineCoordinates.hopfAlgebra E
  let eE := AffineCoordinates.hopfSpecIso E
  let eZ : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R Λ)) ≅ Z :=
    Diagonalizable.hopfSpecIso R Λ ≪≫ eZ0.symm
  let eT : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R Λ')) ≅ T :=
    Diagonalizable.hopfSpecIso R Λ' ≪≫ eT0.symm
  let π : A ⟶ Diagonalizable.hopfAlgebra R Λ :=
    (hopfSpec.fullyFaithful.preimage (eZ.hom ≫ z ≫ eE.symm.hom)).unop
  let φ : Diagonalizable.hopfAlgebra R Λ' ⟶ A :=
    (hopfSpec.fullyFaithful.preimage (eE.symm.inv ≫ p ≫ eT.symm.hom)).unop
  have hπ : (hopfSpec R).map π.op = eZ.hom ≫ z ≫ eE.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hφ : (hopfSpec R).map φ.op = eE.symm.inv ≫ p ≫ eT.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hz' : IsClosedSubgroup ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eZ (hz.comp_iso eE.symm)
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec R).map π.op))
      ((hopfSpec R).map φ.op) := by
    rw [hπ, hφ, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_comp_iso,
      ← Category.assoc]
    exact (hq.comapIso eE.symm).comp_iso eT.symm
  have hext := isExtension_diagonalizable φ π hz' hq'
  have hD : ∀ e : AddMonoidAlgebra K Λ', IsIdempotentElem e → e = 0 ∨ e = 1 := by
    have : IsIso eT0.hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eT0)).hom)
    have hc : ConnectedSpace (Diagonalizable.groupScheme R Λ').X.left :=
      eT0.hom.hom.hom.left.surjective.connectedSpace eT0.hom.hom.hom.left.continuous
    have : ConnectedSpace (PrimeSpectrum (AddMonoidAlgebra K Λ')) := hc
    intro e he
    exact Diagonalizable.SmoothConnectedCriteria.eq_zero_or_one_of_connectedSpace he
  have : Coalgebra.IsCocomm K A := ConnectedExtensionHopf.isCocomm hext hD
  let Y := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of K))
  let f : Y ⟶ E.X := eE.hom.hom.hom
  have : IsMonHom f := eE.hom.hom.isMonHom_hom
  have hgf : eE.inv.hom.hom ≫ f = 𝟙 E.X := congrArg (fun φ => φ.hom.hom) eE.inv_hom_id
  have hfg : f ≫ eE.inv.hom.hom = 𝟙 Y := congrArg (fun φ => φ.hom.hom) eE.hom_inv_id
  have : IsIso f := ⟨eE.inv.hom.hom, hfg, hgf⟩
  have : IsMonHom (asIso f).hom := by simpa using (inferInstance : IsMonHom f)
  exact isCommMonObj_of_iso (asIso f)

end CentralExtensionHopfSpec

/-! ### Base change and descent -/

set_option backward.isDefEq.respectTransparency.types false in
/-- A connected affine group scheme of finite type over a field is geometrically connected. (The
proof repeats the private `geometricallyConnected_of_connected_affine` of
`SmoothConnectedGeometryProof`.) -/
theorem geometricallyConnected_of_connectedSpace (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom]
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] : GeometricallyConnected H.X.hom := by
  let : GrpObj (Over.mk H.X.hom) := H.grp
  obtain ⟨G₀, i, L₀, hi, -, -, -, hgc, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      k (GoodReductionJacobian.relativeGroupLawOfGrpObj k H.X.hom)
  let : IsOpenImmersion i := hi
  have hr : Set.range i = Set.univ := by
    rw [hrange, PreconnectedSpace.connectedComponent_eq_univ]
  have : IsIso i := isIso_of_isOpenImmersion_of_opensRange_eq_top i (by
    ext x
    change x ∈ Set.range i ↔ x ∈ (Set.univ : Set H.X.left)
    rw [hr])
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected) i H.X.hom).mp
    hgc

/-- Base change along a composite is base change along each map in turn. -/
def baseChangeCompIso' {S S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S') (G : GroupScheme S) :
    (GroupScheme.baseChange (c ≫ b)).obj G ≅
      (GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj G) :=
  (Functor.mapGrpNatIso (Over.pullbackComp c b)).app G ≪≫ Functor.mapGrpCompIso.app G

/-- A group of multiplicative type split by `L` becomes diagonalizable over any extension of
`L`: base change along `Spec E → Spec L → Spec k`. -/
def diagonalizableBaseChangeIso {k L E : Type u} [Field k] [Field L] [Field E] [Algebra k L]
    (g : L →+* E) {H : GroupScheme (Spec (CommRingCat.of k))} {N : Type u} [AddCommGroup N]
    (eH : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H ≅
      (Diagonalizable.groupScheme (CommRingCat.of L) N).toGrp) :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H ≅
      (Diagonalizable.groupScheme (CommRingCat.of E) N).toGrp :=
  baseChangeCompIso' _ _ H ≪≫ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom g))).mapIso eH ≪≫
    Diagonalizable.baseChangeIso (Spec.map (CommRingCat.ofHom g)) N

/-- **Extensions with connected quotient are commutative.** Let `k` be a field, `i : H ⟶ G` a
monomorphism and `p : G ⟶ K` an fppf quotient map with kernel the range of `i`. If `H` and `K`
are of multiplicative type and `K` is connected, then `G` is commutative. -/
theorem isCommMonObj_of_connectedSpace {k : Type u} [Field k]
    {H G K : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) (p : G ⟶ K) [Mono i.hom.hom]
    (hq : IsFppfQuotient (SubgroupFunctor.range i) p) (hH : IsMultiplicativeType H)
    (hK : IsMultiplicativeType K) [ConnectedSpace K.X.left] : IsCommMonObj G.X := by
  have : IsAffineHom K.X.hom := hK.isAffineHom
  have : LocallyOfFiniteType K.X.hom := hK.locallyOfFiniteType
  have hgc : GeometricallyConnected K.X.hom := geometricallyConnected_of_connectedSpace k K
  obtain ⟨L₁, _, _, N, _, _, ⟨eH⟩⟩ := hH
  obtain ⟨L₂, _, _, M, _, _, ⟨eK⟩⟩ := hK
  let E := TorusBaseChange.commonExtension k L₁ L₂
  let : Field E.carrier := E.field
  let b₁ := Spec.map (CommRingCat.ofHom (algebraMap k L₁))
  let b₂ := Spec.map (CommRingCat.ofHom (algebraMap k L₂))
  let c₁ := Spec.map (CommRingCat.ofHom E.leftHom)
  let c₂ := Spec.map (CommRingCat.ofHom E.rightHom)
  let b := c₁ ≫ b₁
  have hb : c₂ ≫ b₂ = b := by
    simp only [b, b₁, b₂, c₁, c₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp, E.compatible]
  -- the base change is faithfully flat and quasi-compact
  have h₁ := (let : Algebra k L₁ := inferInstance; fieldExtension_fpqc k L₁)
  have h₂ := (let : Algebra L₁ E.carrier := E.leftHom.toAlgebra; fieldExtension_fpqc L₁ E.carrier)
  have : Surjective b₁ := h₁.1
  have : Flat b₁ := h₁.2.1
  have : QuasiCompact b₁ := h₁.2.2
  have : Surjective c₁ := h₂.1
  have : Flat c₁ := h₂.2.1
  have : QuasiCompact c₁ := h₂.2.2
  -- the diagonalizable models over `E`
  let eHE : (GroupScheme.baseChange b).obj H ≅
      (Diagonalizable.groupScheme (CommRingCat.of E.carrier) N).toGrp :=
    diagonalizableBaseChangeIso E.leftHom eH
  let eKE : (GroupScheme.baseChange b).obj K ≅
      (Diagonalizable.groupScheme (CommRingCat.of E.carrier) M).toGrp :=
    eqToIso (by rw [← hb]) ≪≫ diagonalizableBaseChangeIso E.rightHom eK
  -- the extension after base change
  have hz := IsFppfQuotient.isClosedSubgroup_of_field i hq
  have hzE : IsClosedSubgroup ((GroupScheme.baseChange b).map i) := hz.baseChange b
  have hqE : IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange b).map i))
      ((GroupScheme.baseChange b).map p) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  have : IsClosedImmersion ((GroupScheme.baseChange b).map i).hom.hom.left := hzE
  have : Mono ((GroupScheme.baseChange b).map i).hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom :=
    isAffineHom_of_over_iso ((Grp.forget _).mapIso eHE)
      (Diagonalizable.isAffineHom (CommRingCat.of E.carrier) N)
  have : IsAffineHom ((GroupScheme.baseChange b).obj K).X.hom :=
    isAffineHom_of_over_iso ((Grp.forget _).mapIso eKE)
      (Diagonalizable.isAffineHom (CommRingCat.of E.carrier) M)
  have : IsAffineHom ((GroupScheme.baseChange b).map p).hom.hom.left :=
    hqE.isAffineHom_of_isAffineHom_kernel _
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    rw [← Over.w ((GroupScheme.baseChange b).map p).hom.hom]
    infer_instance
  have : IsAffine ((GroupScheme.baseChange b).obj G).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj G).X.hom
  -- connectedness of the quotient after base change
  have : GeometricallyConnected ((GroupScheme.baseChange b).obj K).X.hom := by
    change GeometricallyConnected (Limits.pullback.snd K.X.hom b)
    infer_instance
  have : ConnectedSpace ((GroupScheme.baseChange b).obj K).X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := ((GroupScheme.baseChange b).obj K).X.hom)
  have hcomm := CentralExtensionHopfSpec.isCommMonObj_of_diagonalizable_connected eHE eKE
    ((GroupScheme.baseChange b).map i) hzE ((GroupScheme.baseChange b).map p) hqE
  exact isCommMonObj_of_baseChange b G hcomm

end Langlands.GroupScheme
