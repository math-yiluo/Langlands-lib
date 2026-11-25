/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceProjective
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.AlgebraicGeometry.FormalModuleSupportConstant
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.FormalSystemClosedSupportPushforward
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedSupportPushforwardSupport
import WeilConjectures.AlgebraicGeometry.CoherentAdicClosedFibreSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Projective compactification algebraization before boundary removal

Source: Stacks Project, Theorem 088E, from Chow compactification through the displayed
support equation (blueprint: new-chow-algebraization-core-support-data).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Construct an algebraization by restricting from a proper compactification, retaining
its degree-zero support on the adic closed fibre.
Source: Stacks Project, Theorem 088E, the paragraphs from "Choose an open immersion"
through the displayed equation for the support intersect V(I).
(blueprint: new-chow-algebraization-core-support-data)

Proof: Factor the supplied quasi-compact immersion into its scheme-theoretic image,
a closed subscheme of the projective space, obtaining an open immersion j:Y -> P.
The closed image P is projective, hence proper over A and Noetherian. Pull back G
termwise. Finite-type pullback support and Nakayama for the successive nilpotent
quotients identify every term's support with q inverse Supp(G_0). This set is proper
over A because q is proper and G_0 has proper support. Its image under j is closed in P.
Extend the terms by j_*: they are coherent by Stacks 0CYJ (coherent open pushforward
on closed support). On j(Y) the quotient compatibility is unchanged; off that closed
support the terms vanish, so the extended terms form a coherent formal system.
Projective existence algebraizes this system to F'. Restrict F' along j to F.
Restriction is coherent and commutes with the ideal-power quotients, yielding the
completion isomorphism on Y. On the adic closed fibre Nakayama identifies Supp(F')
with the support of its first quotient. That quotient is j_*q^*G_0 and has support
inside j(Y), giving the stated containment. No assertion about support away from the
closed fibre is made here; the separate support theorem proves boundary avoidance. -/
theorem exists_chow_algebraization_compactification_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : Z.IdealSheafData)
    (hQ : Q = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (Y : Scheme.{u}) (q : Y ⟶ Z) [IsProper q] (n : ℕ)
    (e : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)))
    [IsImmersion e]
    (he : e ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
      q ≫ f) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (.of A)) (j : Y ⟶ P)
      (F' : CoherentModules P) (F : CoherentModules Y),
      IsNoetherian P ∧ IsProper p ∧ IsOpenImmersion j ∧
      j ≫ p = q ≫ f ∧
      Nonempty ((Scheme.Modules.tensorPullback j).obj F'.obj ≅ F.obj) ∧
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        formalCompletionSystem (Q.comap q) F.obj) ∧
      {x : P | ¬ Subsingleton (F'.obj.presheaf.stalk x)} ∩
        p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆ Set.range j := by
  classical
  let π := (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A))
  -- Use the concrete scheme-theoretic image as the projective compactification.
  let X := e.image
  let p : X ⟶ Spec (.of A) := e.imageι ≫ π
  let j : Y ⟶ X := e.toImage
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (q ≫ f)
  have : QuasiCompact e := QuasiCompact.of_comp e π
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  have hj : j ≫ p = q ≫ f := by
    dsimp [j, p]
    rw [← Category.assoc, e.toImage_imageι]
    exact he
  let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker
  have hkernel : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := by
    dsimp [J]
    rw [Scheme.ker_of_isAffine]
    congr 1
    rw [← RingHom.ker_equiv_comp _
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).commRingCatIsoToRingEquiv]
    rw [RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
      ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
      ← RingHom.comap_ker]
    change (RingHom.ker (Ideal.Quotient.mk I)).comap
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom = _
    rw [Ideal.mk_ker]
    exact (Ideal.map_symm
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv).symm
  have hQ' : Q = J.comap f := by
    rw [hkernel]
    exact hQ
  obtain ⟨⟨Pq, _, hPq, _, _⟩, _⟩ := exists_formalSystemsPullback q Q
  let GY := Pq.obj G
  have hF : GY.obj = G.obj ⋙ Scheme.Modules.tensorPullback q :=
    congrArg (fun R ↦ R.obj G) hPq
  obtain ⟨R, hRset, hRproper⟩ := hR
  let RY := R.preimage (f := q.base) q.continuous
  have hRY : Scheme.IsClosedSubsetProperOver (q ≫ f) RY :=
    (Scheme.isClosedSubsetProperOver_union_preimage (q ≫ f)).2 q f rfl R hRproper
  obtain ⟨T, hTset, _⟩ :=
    (Scheme.closed_subset_proper_over_base_properties (q ≫ f) RY).2.2.2 j p hj hRY
  have hT : (T : Set X) ⊆ Set.range j.base := by
    rw [hTset]
    exact Set.image_subset_range _ _
  have hcoh := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z
    (G.obj.obj (op 0))).mp (G.property.1 0)
  have : (G.obj.obj (op 0)).IsQuasicoherent := hcoh.1
  have : (G.obj.obj (op 0)).IsFiniteType := hcoh.2
  have hsupport : ∀ n : ℕ,
      {y : Y | ¬ Subsingleton ((GY.obj.obj (op n)).presheaf.stalk y)} ⊆
        j.base ⁻¹' (T : Set X) := by
    intro n y hy
    have hy0 : y ∈ {y : Y | ¬ Subsingleton ((GY.obj.obj (op 0)).presheaf.stalk y)} := by
      rw [← formalModule_support_eq (Q.comap q) GY n]
      exact hy
    have hyR : y ∈ (RY : Set Y) := by
      change y ∈ q.base ⁻¹' (R : Set Z)
      rw [hRset]
      have hs := (Scheme.Modules.finiteType_module_support_pullback
        (G.obj.obj (op 0))).2.2 Y q |>.2
      rw [hF] at hy0
      rw [← hs]
      exact hy0
    rw [hTset]
    exact ⟨y, hyR, rfl⟩
  have hK : (J.comap p).comap j = Q.comap q := by
    rw [← Scheme.IdealSheafData.comap_comp, hj,
      Scheme.IdealSheafData.comap_comp, ← hQ']
  have hpush : IsCoherentFormalModule (J.comap p)
      (GY.obj ⋙ Scheme.Modules.pushforward j) := by
    apply coherentFormal_pushforward_of_closed_support j (J.comap p) GY.obj
      T hT hsupport
    rw [hK]
    exact GY.property
  let H : CoherentFormalModule X (J.comap p) :=
    ⟨GY.obj ⋙ Scheme.Modules.pushforward j, hpush⟩
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction j
  let α : Scheme.Modules.tensorPullback j ≅ Scheme.Modules.restrictFunctor j :=
    adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction j)
  let ε : Scheme.Modules.pushforward j ⋙ Scheme.Modules.tensorPullback j ≅ 𝟭 Y.Modules :=
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward j) α ≪≫
      asIso (Scheme.Modules.restrictAdjunction j).counit
  have hH : G.obj ⋙ Scheme.Modules.tensorPullback q ≅
      H.obj ⋙ Scheme.Modules.tensorPullback j := by
    change G.obj ⋙ Scheme.Modules.tensorPullback q ≅
      (GY.obj ⋙ Scheme.Modules.pushforward j) ⋙ Scheme.Modules.tensorPullback j
    exact (eqToIso hF).symm ≪≫ (Functor.rightUnitor GY.obj).symm ≪≫
      Functor.isoWhiskerLeft GY.obj ε.symm ≪≫
        (Functor.associator GY.obj _ _).symm
  have hJ : (J.comap p).comap j = Q.comap q := by
    rw [← Scheme.IdealSheafData.comap_comp, hj, Scheme.IdealSheafData.comap_comp, ← hQ']
  have : (completion X (J.comap p)).IsEquivalence :=
    completion_isEquivalence_of_projective_embedding A I X n e.imageι
  -- Projective existence algebraizes the extended system on the compactification.
  let F' := (completion X (J.comap p)).objPreimage H
  let β := (ObjectProperty.ι (IsCoherentFormalModule (J.comap p))).mapIso
    ((completion X (J.comap p)).objObjPreimageIso H).symm
  obtain ⟨⟨P, C, hP, hC, ⟨α⟩⟩, _⟩ := exists_formalSystemsPullback j (J.comap p)
  let F := C.obj F'
  -- Compare restriction of completion with completion of the coherent restriction.
  let γ := (ObjectProperty.ι (IsCoherentFormalModule ((J.comap p).comap j))).mapIso
    (α.app F')
  have hPo : (P.obj ((completion X (J.comap p)).obj F')).obj =
      formalCompletionSystem (J.comap p) F'.obj ⋙ Scheme.Modules.tensorPullback j :=
    congrArg (fun T ↦ T.obj ((completion X (J.comap p)).obj F')) hP
  change (P.obj ((completion X (J.comap p)).obj F')).obj ≅
    formalCompletionSystem ((J.comap p).comap j) F.obj at γ
  rw [hPo, hJ] at γ
  have hCompletion : Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
      formalCompletionSystem (Q.comap q) F.obj) := by
    refine ⟨hH ≪≫ ?_ ≪≫ γ⟩
    exact ((Functor.whiskeringRight ℕᵒᵖ X.Modules Y.Modules).obj
      (Scheme.Modules.tensorPullback j)).mapIso β
  have hRestriction : (Scheme.Modules.tensorPullback j).obj F'.obj = F.obj :=
    (congrArg (fun T ↦ T.obj F') hC).symm
  refine ⟨X, p, j, F', F, inferInstance, inferInstance, inferInstance, hj,
    ⟨eqToIso hRestriction⟩, hCompletion, ?_⟩
  intro x hx
  have hx := coherent_adic_closed_fibre_support A I p F' hx
  have hxH : ¬ Subsingleton ((H.obj.obj (op 0)).presheaf.stalk x) := by
    let b := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapIso (β.app (op 0))
    apply (not_congr b.toLinearEquiv.toEquiv.subsingleton_congr).mpr
    change ¬ Subsingleton ((formalModuleQuotient (J.comap p) 1 F'.obj).presheaf.stalk x)
    rw [hkernel]
    exact hx
  exact hT (Scheme.Modules.pushforward_support_subset_of_closed_support j
    (GY.obj.obj (op 0)) T (hsupport 0) hxH)


end AlgebraicGeometry
