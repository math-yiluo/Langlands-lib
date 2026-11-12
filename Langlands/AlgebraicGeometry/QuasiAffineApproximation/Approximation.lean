import Langlands.AlgebraicGeometry.QuasiAffineApproximation.Skeleton
import Langlands.AlgebraicGeometry.QuasiAffineApproximation.SeparatedQuotient
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantQuotientCoverDescent
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSchemeQuotientMap
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationFiniteTypeSystem
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleTailNextSystem
import Langlands.AlgebraicGeometry.RingEtaleGroupoidFiniteCover
import Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation.AffinePinching
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianCoaction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Noetherian approximation of a finite cover with quasi-affine quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.QuasiAffineApproximation

open EtaleEquivalenceRelation

/-- A flat, locally finitely presented surjection whose kernel pair is the relation is a scheme
quotient: it is étale because `t` is. -/
def schemeQuotientOfIsPullback (F : EtaleEquivalenceRelation.{u}) {M : Scheme.{u}}
    (q : F.U ⟶ M) (hpb : IsPullback F.t F.s q q) [Flat q] [LocallyOfFinitePresentation q]
    [Surjective q] : F.SchemeQuotient :=
  have : IsZariskiLocalAtTarget @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtTarget _
  have : Etale q := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hpb
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ F.etale_t
  { M := M, q := q, isPullback := hpb }

section Level

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ EtaleEquivalenceRelation.{u})
  (c : Cone D) [∀ i, IsAffine (D.obj i).U] [∀ i, IsAffine (D.obj i).R]
  [∀ i, LocallyOfFiniteType (terminal.from (D.obj i).U)]
  (hc : IsLimit (objectFunctor.mapCone c))

include hc in
/-- If the limit of a cofiltered diagram of affine relations of finite type over `ℤ` has a
quasi-affine quotient with affine quotient map, then some level has a quasi-affine quotient
with affine quotient map. -/
theorem exists_level_quasiAffine_quotient (Qc : c.pt.SchemeQuotient) [IsAffineHom Qc.q]
    [Qc.M.IsQuasiAffine] :
    ∃ (i : I) (Q : (D.obj i).SchemeQuotient), IsAffineHom Q.q ∧ Q.M.IsQuasiAffine := by
  let 𝒰 := Qc.M.affineCover.finiteSubcover
  let W : 𝒰.I₀ → Qc.M.Opens := fun k => (𝒰.f k).opensRange
  have hWaff : ∀ k, IsAffineOpen (W k) := fun k => isAffineOpen_opensRange (𝒰.f k)
  let U : 𝒰.I₀ → c.pt.U.Opens := fun k => Qc.q ⁻¹ᵁ W k
  have hUcov : TopologicalSpace.IsOpenCover U := by
    change (⨆ k, Qc.q ⁻¹ᵁ W k) = ⊤
    rw [← Scheme.Hom.preimage_iSup, 𝒰.iSup_opensRange, Scheme.Hom.preimage_top]
  obtain ⟨i, V, hVcov, hV⟩ := CartesianDiagram.exists_invariantAffineQuotientCover D c hc U
    hUcov (fun k => (hWaff k).preimage Qc.q) (fun k => Qc.isInvariantOpen_preimage (W k))
    (fun k => Qc.hasAffineQuotient_chart (W k) (hWaff k))
  let Qi := (D.obj i).schemeQuotientOfInvariantOpenCover V hVcov (fun k => (hV k).2.1)
    (fun k => (hV k).2.2.2)
  have : IsAffineHom Qi.q := Qi.isAffineHom_q_of_invariantOpenCover V hVcov
    (fun k => (hV k).2.1) (fun k => (hV k).1) (fun k => (hV k).2.2.2)
  let A := CartesianDiagram.above D i
  let C := c.whisker (Over.forget i)
  have hlim : IsLimit (objectFunctor.mapCone C) := CartesianDiagram.isLimitObjectAbove D i c hc
  have : ∀ j : Over i, IsAffine (A.obj j).U := fun j => inferInstanceAs (IsAffine (D.obj j.left).U)
  have : ∀ j : Over i, IsAffine (A.obj j).R := fun j => inferInstanceAs (IsAffine (D.obj j.left).R)
  have : ∀ j : Over i, CompactSpace (A.obj j).U := fun j => inferInstance
  have : ∀ j : Over i, LocallyOfFiniteType (terminal.from (A.obj j).U) := fun j =>
    inferInstanceAs (LocallyOfFiniteType (terminal.from (D.obj j.left).U))
  let Q : ∀ j : Over i, (A.obj j).SchemeQuotient := fun j =>
    SchemeQuotient.ofIsCartesianHom (D.map j.hom).isCartesian Qi
  have hQ : ∀ j, IsAffineHom (Q j).q := fun j =>
    SchemeQuotient.isAffineHom_q (D.map j.hom).isCartesian (Q j) Qi
  let F := SchemeQuotient.quotientFunctor A Q
  let Qc' : C.pt.SchemeQuotient := Qc
  have hF : IsLimit (SchemeQuotient.quotientCone Q C Qc') :=
    SchemeQuotient.isLimitQuotientCone Q C Qc' hlim
  have : ∀ {j k : Over i} (a : j ⟶ k), IsAffineHom (F.map a) := fun a =>
    SchemeQuotient.isAffineHom_map (A.map a).isCartesian _ _
  have : ∀ j, CompactSpace (F.obj j) := fun j => SchemeQuotient.compactSpace (Q j)
  have : ∀ j, LocallyOfFiniteType (terminal.from (F.obj j)) := fun j =>
    SchemeQuotient.locallyOfFiniteType_terminal (Q j)
  obtain ⟨j, -, ⟨Mdl⟩⟩ := AbsoluteNoetherianApproximation.exists_finiteTypeOpenModel_of_isLimit
    F _ hF Qc.M.toSpecΓ ∅ Set.finite_empty (Over.mk (𝟙 i))
  have : CompactSpace (Q j).M := SchemeQuotient.compactSpace (Q j)
  have : (Q j).M.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion Mdl.e
  exact ⟨j.left, Q j, hQ j, this⟩

end Level

/-- Part II: the Noetherian approximation of a finite surjective cartesian cover whose cover
has a quasi-affine quotient. -/
theorem approximationInterface : ApproximationInterface.{u} := by
  intro E E' φ g M q _ hcart _ _ _ hpb _ _ _
  have : IsAffine E'.U := isAffine_of_isAffineHom φ
  have : IsClosedImmersion (prod.lift E.t E.s) :=
    isClosedImmersion_lift_of_separated_quotient hcart q hpb
  have : IsAffine E.R := E.isAffine_relation
  have : IsSeparated E.s := inferInstance
  obtain ⟨L⟩ := E.nonempty_affineFiniteTypeFirstLevel_of_tupleTail_systems
    E.tupleLengthBound (fun p hp M =>
      E.nonempty_finiteTypeCartesianSystem_tupleTailNext E.tupleLengthBound p le_rfl hp M)
  have h : IsCartesianHom E L.relation L.comparison.objMap L.comparison.relMap :=
    L.comparison.isCartesian
  have hc := hcart.comp h
  have : IsNoetherianRing Γ(L.relation.U, ⊤) := inferInstance
  let := hc.stableIndex_isCofiltered
  have : ∀ i, LocallyOfFiniteType (terminal.from (hc.stableDiagram.obj i).U) :=
    hc.stableDiagram_locallyOfFiniteType
  have : IsAffineHom q := by
    have : IsAffineHom (q ≫ terminal.from M) := isAffineHom_of_isAffine _
    exact IsAffineHom.of_comp q (terminal.from M)
  let Qc : E'.SchemeQuotient := schemeQuotientOfIsPullback E' q hpb
  have : IsAffineHom Qc.q := inferInstanceAs (IsAffineHom q)
  have : Qc.M.IsQuasiAffine := inferInstanceAs M.IsQuasiAffine
  obtain ⟨i, Q, hQ, hQM⟩ := exists_level_quasiAffine_quotient hc.stableDiagram hc.stableCone
    hc.stableCone_isLimitObject Qc
  -- the ring-level finite surjective cover through the level `i`
  let := L.relation.s.appTop.hom.toAlgebra
  let := L.comparison.objMap.appTop.hom.toAlgebra
  let := (φ ≫ L.comparison.objMap).appTop.hom.toAlgebra
  have hE₀ := L.relation.ringEtaleGroupoid
  let ψ := appTopAlgHom φ L.comparison.objMap
  have hψ : ∀ b, hc.coaction.coaction (ψ b) =
      Algebra.TensorProduct.map (AlgHom.id Γ(L.relation.U, ⊤) Γ(L.relation.R, ⊤)) ψ
        (h.coaction.coaction b) :=
    fun b => hcart.ringHom_comp_appTop h b
  have hfin : (ψ : Γ(E.U, ⊤) →+* Γ(E'.U, ⊤)).Finite :=
    IsFinite.finite_app φ ⊤ (isAffineOpen_top E.U)
  have hsurj : Function.Surjective (PrimeSpectrum.comap (ψ : Γ(E.U, ⊤) →+* Γ(E'.U, ⊤))) := by
    have : Surjective (Spec.map φ.appTop) :=
      (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine φ)).mp
        inferInstance
    exact (surjective_iff _).mp this
  have hker := RingEtaleGroupoid.ker_le_nilradical_of_comap_surjective _ hsurj
  obtain ⟨s, hs⟩ := i.unop.2.1
  obtain ⟨D, D', hD, hD', φD, hDfg, hsD', hφD, hφfin, hφsurj⟩ :=
    hE₀.exists_finite_level h.coaction h.coaction_isMultiplicative hc.coaction
      hc.coaction_isMultiplicative ψ hψ hfin hker s
  have hD'fg : D'.FG := by
    rw [Subalgebra.fg_iff_finiteType, ← RingHom.finiteType_algebraMap,
      ← φD.comp_algebraMap]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_finite hφfin)
      (RingHom.finiteType_algebraMap.mpr ((Subalgebra.fg_iff_finiteType D).mp hDfg))
  let j : hc.stableIndex := ⟨D', hD'fg, hD'⟩
  let jD : h.stableIndex := ⟨D, hDfg, hD⟩
  have hij : i.unop ≤ j := by
    change i.unop.1 ≤ D'
    rw [← hs]
    exact Algebra.adjoin_le hsD'
  let a : Opposite.op j ⟶ i := (homOfLE hij).op
  let Q₁ := SchemeQuotient.ofIsCartesianHom (hc.stableDiagram.map a).isCartesian Q
  have : IsAffineHom Q₁.q := SchemeQuotient.isAffineHom_q (hc.stableDiagram.map a).isCartesian Q₁ Q
  have : IsAffineHom (SchemeQuotient.map (hc.stableDiagram.map a).isCartesian Q₁ Q) :=
    SchemeQuotient.isAffineHom_map _ _ _
  have hM₁ : Q₁.M.IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (SchemeQuotient.map (hc.stableDiagram.map a).isCartesian Q₁ Q)
  have : CompactSpace Q₁.M := SchemeQuotient.compactSpace Q₁
  have : LocallyOfFiniteType (terminal.from Q₁.M) := SchemeQuotient.locallyOfFiniteType_terminal Q₁
  have : IsLocallyNoetherian Q₁.M :=
    AbsoluteNoetherianApproximation.isLocallyNoetherian_of_locallyOfFiniteType Q₁.M
  let leg := hc.stableCone.π.app (Opposite.op j)
  have : IsAffine (((Functor.const _).obj hc.stableCone.pt).obj (Opposite.op j)).U :=
    inferInstanceAs (IsAffine E'.U)
  have : IsAffineHom leg.objMap := isAffineHom_of_isAffine _
  have : IsAffineHom (SchemeQuotient.map leg.isCartesian Qc Q₁) :=
    SchemeQuotient.isAffineHom_map _ _ _
  refine ⟨h.stableDiagram.obj (Opposite.op jD), hc.stableDiagram.obj (Opposite.op j),
    Spec.map (CommRingCat.ofHom (φD : D →+* D')), _, Q₁.M, Q₁.q,
    (h.stableCone.π.app (Opposite.op jD)).objMap, leg.objMap,
    SchemeQuotient.map leg.isCartesian Qc Q₁, inferInstance, inferInstance,
    RingEtaleGroupoid.isCartesianHom_of_equivariant
      (by exact hE₀.level _ (hE₀.subalgebraCoaction_isMultiplicative _
        h.coaction_isMultiplicative _ _))
      (by exact hE₀.level _ (hE₀.subalgebraCoaction_isMultiplicative _
        hc.coaction_isMultiplicative _ _)) φD
      (hE₀.subalgebraCoaction_map h.coaction hc.coaction ψ hψ hD hD' φD hφD),
    (IsFinite.SpecMap_iff _).mpr hφfin, (surjective_iff _).mpr hφsurj, hM₁, ⟨⟩,
    Q₁.isPullback, inferInstance, inferInstance, inferInstance, ?_,
    SchemeQuotient.q_map leg.isCartesian Qc Q₁, inferInstance⟩
  change (E'.U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom D'.val.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (φD : D →+* D')) =
    φ ≫ E.U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom D.val.toRingHom)
  have hcomp : CommRingCat.ofHom (φD : D →+* D') ≫ CommRingCat.ofHom D'.val.toRingHom =
      CommRingCat.ofHom D.val.toRingHom ≫ φ.appTop := by
    ext d
    exact hφD d
  rw [Category.assoc, ← Spec.map_comp, hcomp, Spec.map_comp, ← Category.assoc,
    Scheme.isoSpec_hom_naturality, Category.assoc]

end Langlands.AlgebraicGeometry.QuasiAffineApproximation
