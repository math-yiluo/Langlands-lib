/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Over

import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Relative profinite test schemes

Source: RefactorInstruction, Section 4, equations finite-XI and XS, Lemma lem:XS;
ModuleObject/Basic.lean, module docstring, lines 38–52; Stacks Project, Tag 097D
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

-- Continuous functors to a subcanonical site preserve finite coproducts:
-- pull back representables, restrict to the extensive topology, and use Yoneda.
private theorem coproducts_of_hom_sheaves {D : Type*} [Category* D]
    (F : Profinite.{u} ⥤ D)
    (hF : ∀ Y, Presieve.IsSheaf (extensiveTopology Profinite) (F.op ⋙ yoneda.obj Y))
    (A : Type u) [Finite A] : PreservesColimitsOfShape (Discrete A) F := by
  constructor
  intro K
  constructor
  intro c hc
  constructor
  refine (F.mapCocone c).isColimitYonedaEquiv.symm ?_
  intro Y
  have : PreservesFiniteProducts (F.op ⋙ yoneda.obj Y) :=
    (Presieve.isSheaf_iff_preservesFiniteProducts _).mp (hF Y)
  have : PreservesLimitsOfShape (Discrete A) (F.op ⋙ yoneda.obj Y) := inferInstance
  have : PreservesLimitsOfShape (Discrete A)ᵒᵖ (F.op ⋙ yoneda.obj Y) :=
    preservesLimitsOfShape_of_equiv (Discrete.opposite A).symm _
  exact isLimitOfPreserves (F.op ⋙ yoneda.obj Y) hc.op

private theorem coproducts_of_continuous {D : Type*} [Category* D]
    (F : Profinite.{u} ⥤ D) (J : GrothendieckTopology D) [J.Subcanonical]
    [F.IsContinuous (coherentTopology Profinite) J] (A : Type u) [Finite A] :
    PreservesColimitsOfShape (Discrete A) F := by
  have hle : extensiveTopology Profinite.{u} ≤ coherentTopology Profinite.{u} := by
    rw [extensiveTopology, ← extensive_regular_generate_coherent]
    exact (Coverage.gi Profinite).gc.monotone_l le_sup_left
  apply coproducts_of_hom_sheaves
  intro Y
  apply Presieve.isSheaf_of_le _ hle
  exact F.op_comp_isSheaf_of_isSheaf_type (coherentTopology Profinite)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj Y))

private theorem lc_limit {I : Type u} [SmallCategory I] [IsCofiltered I]
    {D : I ⥤ Profinite.{u}} (c : Cone D) (hc : IsLimit c)
    (hs : ∀ i, Function.Surjective (c.π.app i)) :
    Nonempty (IsLimit (profiniteToCommRingCatOp.mapCone c)) := by
  let t := coconeLeftOpOfCone (profiniteToCommRingCatOp.mapCone c)
  have ht : IsColimit t := by
    have : ReflectsColimitsOfShape Iᵒᵖ (forget CommRingCat.{u}) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    apply isColimitOfReflects (forget CommRingCat.{u})
    refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
    · intro f
      obtain ⟨i, g, h⟩ := Profinite.exists_locallyConstant c hc f
      exact ⟨Opposite.op i, g, h⟩
    · intro i f g h
      refine ⟨i, 𝟙 i, ?_⟩
      suffices f = g by simpa using this
      exact LocallyConstant.comap_injective (c.π.app i.unop).hom.hom (hs i.unop) h
  exact ⟨isLimitConeOfCoconeLeftOp _ ht⟩

private abbrev point : Profinite.{u} := Profinite.of PUnit.{u + 1}
private def pointMap (S : Profinite.{u}) (s : S) : point ⟶ S :=
  CompHausLike.ofHom _ ⟨fun _ ↦ s, continuous_const⟩
private abbrev finiteCofan (S : FintypeCat.{u}) :
    Cofan (fun _ : S ↦ point.{u}) :=
  Cofan.mk (FintypeCat.toProfinite.obj S) (fun s : S ↦ pointMap (FintypeCat.toProfinite.obj S) s)

set_option backward.isDefEq.respectTransparency false in
private def finiteCofanIsColimit (S : FintypeCat.{u}) : IsColimit (finiteCofan S) := by
  let : TopologicalSpace S := FintypeCat.botTopology S
  have : DiscreteTopology S := FintypeCat.discreteTopology S
  refine Cofan.IsColimit.mk _ (fun t ↦ CompHausLike.ofHom _
    ⟨fun s ↦ t.inj s PUnit.unit, continuous_of_discreteTopology⟩) ?_ ?_
  · intro t s
    ext x
    exact congrArg (t.inj s) (Subsingleton.elim _ _)
  · intro t m hm
    ext s
    exact ConcreteCategory.congr_hom (hm s) PUnit.unit

set_option backward.isDefEq.respectTransparency false in
private theorem finiteIso {C : Type*} [Category* C] [HasCoproducts.{u} C]
    (F : Profinite.{u} ⥤ C)
    (hF : ∀ (A : Type u) [Finite A], PreservesColimitsOfShape (Discrete A) F) :
    Nonempty (FintypeCat.toProfinite ⋙ F ≅
      forget FintypeCat.{u} ⋙ sigmaConst.obj (F.obj point)) := by
  have (A : Type u) [Finite A] := hF A
  let hi (S : FintypeCat.{u}) :=
    isColimitCofanMkObjOfIsColimit F _ _ (finiteCofanIsColimit S)
  let e (S : FintypeCat.{u}) :
      (sigmaConst.obj (F.obj point)).obj S ≅ F.obj (FintypeCat.toProfinite.obj S) :=
    (coproductIsCoproduct (fun _ : S ↦ F.obj point)).coconePointUniqueUpToIso (hi S)
  have he (S : FintypeCat.{u}) (s : S) :
      Sigma.ι (fun _ : S ↦ F.obj point) s ≫ (e S).hom =
        F.map (pointMap (FintypeCat.toProfinite.obj S) s) :=
    (coproductIsCoproduct (fun _ : S ↦ F.obj point)).comp_coconePointUniqueUpToIso_hom
      (hi S) ⟨s⟩
  refine ⟨(NatIso.ofComponents e ?_).symm⟩
  intro S T f
  apply Sigma.hom_ext
  intro s
  change Sigma.ι (fun _ : S ↦ F.obj point) s ≫
      (Sigma.map' f (fun _ ↦ 𝟙 (F.obj point))) ≫ (e T).hom =
    Sigma.ι (fun _ : S ↦ F.obj point) s ≫ (e S).hom ≫ F.map (FintypeCat.toProfinite.map f)
  rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, he,
    ← Category.assoc, he, ← F.map_comp]
  congr 1

private theorem spec_joint_surjective (A : Type*) (S : A → Profinite.{u}) (T : Profinite.{u})
    (f : ∀ a, S a ⟶ T) (hf : ∀ t : T, ∃ a s, f a s = t) :
    ∀ t : profiniteToScheme.obj T,
      ∃ a, t ∈ Set.range (profiniteToScheme.map (f a)) := by
  intro t
  let e := LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)
  obtain ⟨a, s, hs⟩ := hf (e.symm t).1
  refine ⟨a, LocallyConstant.toPrimeSpectrum (s, (e.symm t).2), ?_⟩
  change PrimeSpectrum.comap (LocallyConstant.comapRingHom (f a).hom.hom)
    (LocallyConstant.toPrimeSpectrum (s, (e.symm t).2)) = t
  conv_rhs => rw [← e.apply_symm_apply t]
  change PrimeSpectrum.comap (LocallyConstant.comapRingHom (f a).hom.hom)
    (PrimeSpectrum.comap (LocallyConstant.evalRingHom s) (e.symm t).2) =
    PrimeSpectrum.comap (LocallyConstant.evalRingHom (e.symm t).1) (e.symm t).2
  ext h
  change h (f a s) ∈ (e.symm t).2.asIdeal ↔ h (e.symm t).1 ∈ (e.symm t).2.asIdeal
  rw [hs]

private theorem spec_cover (A : Type*) [Finite A] (S : A → Profinite.{u}) (T : Profinite.{u})
    (f : ∀ a, S a ⟶ T) (hf : ∀ t : T, ∃ a s, f a s = t) :
    Presieve.ofArrows (fun a ↦ profiniteToScheme.obj (S a))
      (fun a ↦ profiniteToScheme.map (f a)) ∈ Scheme.fpqcPrecoverage _ := by
  have hw (a : A) : WeaklyEtale (profiniteToScheme.map (f a)) := by
    apply MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale)
      (profiniteToScheme.map (f a)) (toSpecZ (profiniteToScheme.obj T))
    · infer_instance
    · rw [comp_toSpecZ]
      infer_instance
  let U : (profiniteToScheme.obj T).Cover (Scheme.precoverage @Flat) :=
    { I₀ := A
      X a := profiniteToScheme.obj (S a)
      f a := profiniteToScheme.map (f a)
      mem₀ := (Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨spec_joint_surjective A S T f hf, fun a ↦ inferInstance⟩ }
  have : Finite U.I₀ := inferInstanceAs (Finite A)
  have (a : A) : IsAffineHom (profiniteToScheme.map (f a)) :=
    inferInstanceAs (IsAffineHom (Spec.map
      (CommRingCat.ofHom (LocallyConstant.comapRingHom (f a).hom.hom :
        LocallyConstant T ℤ →+* LocallyConstant (S a) ℤ))))
  have : ∀ i, QuasiCompact (U.f i) := fun i ↦
    inferInstanceAs (QuasiCompact (profiniteToScheme.map (f i)))
  have : QuasiCompactCover U.toPreZeroHypercover := QuasiCompactCover.of_finite
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr this, U.mem₀⟩

private theorem profinite_cover_preserving :
    CoverPreserving (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
      profiniteToProEt := by
  constructor
  intro T R hR
  obtain ⟨A, _, S, f, hf, hmem⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily R).mp hR
  have hjs : ∀ t : T, ∃ a s, f a s = t :=
    ((Profinite.effectiveEpiFamily_tfae S f).out 1 3).mp hf
  have hcover : Presieve.ofArrows (fun a ↦ profiniteToProEt.obj (S a))
      (fun a ↦ profiniteToProEt.map (f a)) ∈ Scheme.ProEt.precoverage specZ _ := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    refine ⟨(spec_cover A S T f hjs).1, ?_⟩
    apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
    refine ⟨spec_joint_surjective A S T f hjs, ?_⟩
    intro a
    apply MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale)
      (profiniteToScheme.map (f a)) (toSpecZ (profiniteToScheme.obj T))
    · infer_instance
    · rw [comp_toSpecZ]
      infer_instance
  apply (Scheme.ProEt.topology specZ).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hcover)
  apply (Sieve.generate_le_iff _ _).mpr
  intro W g hg
  obtain ⟨a⟩ := hg
  exact ⟨S a, f a, 𝟙 _, hmem a, (Category.id_comp _).symm⟩

local instance (X : Scheme.{u}) : HasCoproducts.{u} (Over X) :=
  fun _ ↦ Over.instHasColimitsOfShape

/-- The relative profinite test functor is independent of finite-quotient presentation,
preserves finite limits and finite disjoint unions, and takes finite jointly surjective
families to fpqc coverings. Its restriction to finite sets is naturally the coproduct of
copies of `X` over `X`; for every cofiltered finite-quotient presentation, the image cone
is limiting over `X`. These two clauses identify its value with the required relative
inverse limit, with canonical comparison isomorphisms respecting all projections.
The functor already supplies weakly etale structure maps, identity and composition laws.
Over `Spec ℤ` the last natural isomorphism identifies it with `Spec LC(-, ℤ)`;
`profiniteToScheme` sends a continuous map to the spectrum of precomposition.

Source: RefactorInstruction, Section 4, equations finite-XI and XS, Lemma lem:XS;
ModuleObject/Basic.lean, lines 38–52; Stacks Project, Tag 097D
(auxiliary; not a blueprint node).

Proof plan (the ten steps of the node):
1. Use `lem-weil-pbc-profinite-limit-function-factorization` and
   `lem-weil-pbc-profinite-clopen-basis` to express locally constant functions as the
   filtered colimit over finite quotients, also over all finite clopen partitions.
2. Form finite coproducts over the partitions, adjoining `X` as a least stage.
   `lem-weil-pbc-finite-affine-coproduct-spectrum`,
   `lem-weil-pbc-morphism-affine-schemes-affine`, and `pqf-lem-affine-local-target`
   make the transitions affine. `lem-weil-pbc-limit-affine-transition-core` gives the limit.
3. Use `lem-weil-pbc-limit-cone-affine-projections-opens` and
   `lem-weil-pbc-spec-small-colimit-limit` to compute its restriction to `Spec R` as
   `Spec LC(S,R)`. `lem-weil-pbc-scheme-morphism-gluing` proves the limit property for
   every finite-quotient presentation, without any compactness assumption on `X`.
4. Precomposition and `def-weil-affine-spectrum` give the local maps; glue them by
   `lem-weil-pbc-scheme-morphism-gluing`. The ring-map identities give functoriality
   and the functorial identification over `Spec ℤ`.
5. Compute the tensor product formulas using finite clopen partitions, compactness
   (`lem-weil-pbc-tychonoff-product-quasi-compact`) and the clopen basis. Apply
   `lem-weil-pbc-spec-small-colimit-limit` and glue to obtain products over `X`.
6. Extend locally constant functions from a closed subspace using the clopen basis.
   For an equalizer, characteristic functions generate the kernel of restriction.
   The spectrum theorem and gluing give equalizers; these and products give finite limits.
7. `lem-weil-pbc-locally-constant-prime-spectrum` identifies points as `(s,p)`.
   `lem-weil-pbc-affine-open-stalk-localization` identifies stalks with `R_p` by
   evaluation, with inverse given by constants. Hence the induced stalk maps are flat
   (`def-weil-flat-morphism`).
8. Apply the finite-limit formula to the diagonal. Step 7 makes it flat, so the
   maps are weakly etale (`definition-ind-etale-pro-etale-weakly--3`) and lie in the recorded
   small pro-etale site (`definition-small-pro-etale-site--1`).
9. Finite jointly surjective families remain jointly surjective on the points `(s,p)`.
   Their arrows are affine (`pqf-def-affine-morphism`, `pqf-lem-affine-local-target`,
   and `lem-weil-pbc-morphism-affine-schemes-affine`) and flat, so their affine
   preimages verify `def-weil-pbc-fpqc-covering`, including the empty family.
10. Restriction gives `LC(S ⊔ T,R) = LC(S,R) × LC(T,R)`.
    Use `lem-weil-pbc-finite-affine-coproduct-spectrum` and gluing for disjoint unions.
    The empty space gives the zero ring and the empty scheme. -/
theorem profinite_test_object_functor (X : Scheme.{u}) :
    PreservesFiniteLimits (profiniteToProEtOf X) ∧
    (∀ (A : Type u) [Finite A],
      PreservesColimitsOfShape (Discrete A) (profiniteToProEtOf X)) ∧
    Nonempty
      (FintypeCat.toProfinite ⋙ profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ≅
        forget FintypeCat.{u} ⋙ sigmaConst.obj (Over.mk (𝟙 X))) ∧
    (∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
      (D : I ⥤ FintypeCat.{u}) (c : Cone (D ⋙ FintypeCat.toProfinite)),
      IsLimit c → (∀ i : I, Function.Surjective (c.π.app i)) →
      Nonempty (IsLimit
        ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X).mapCone c))) ∧
    (∀ (A : Type u) [Finite A] (S : A → Profinite.{u}) (T : Profinite.{u})
      (f : ∀ a : A, S a ⟶ T),
      (∀ t : T, ∃ (a : A) (s : S a), f a s = t) →
      Presieve.ofArrows
        (fun a ↦ (profiniteToProEtOf X |>.obj (S a)).left)
        (fun a ↦ (profiniteToProEtOf X |>.map (f a)).left) ∈
        Scheme.fpqcPrecoverage ((profiniteToProEtOf X).obj T).left) ∧
    Nonempty
      (profiniteToProEtOf specZ.{u} ⋙ Scheme.ProEt.forget specZ ⋙ Over.forget specZ ≅
        profiniteToScheme.{u}) := by
  have hlimits : PreservesFiniteLimits (profiniteToProEtOf X) := by
    have : PreservesFiniteLimits profiniteToProEt.{u} := inferInstance
    have : PreservesFiniteLimits
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) := inferInstance
    exact comp_preservesFiniteLimits _ _
  have : profiniteToProEt.{u}.IsContinuous (coherentTopology Profinite)
      (Scheme.ProEt.topology specZ) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      profinite_cover_preserving
  have := Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  have hcont : (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite)
      (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology specZ) _
  have hcop (A : Type u) [Finite A] :
      PreservesColimitsOfShape (Discrete A) (profiniteToProEtOf X) :=
    coproducts_of_continuous _ (Scheme.ProEt.topology X) A
  refine ⟨hlimits, hcop, ?_, ?_, ?_, ?_⟩
  · let F := profiniteToProEtOf X ⋙ Scheme.ProEt.forget X
    have : F.IsContinuous (coherentTopology Profinite) (Scheme.proetaleTopology.over X) :=
      Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
    have hF (A : Type u) [Finite A] : PreservesColimitsOfShape (Discrete A) F :=
      coproducts_of_continuous F (Scheme.proetaleTopology.over X) A
    have : PreservesFiniteLimits F := inferInstance
    let e : F.obj point ≅ Over.mk (𝟙 X) :=
      (Profinite.isTerminalPUnit.isTerminalObj F _).uniqueUpToIso Over.mkIdTerminal
    exact ⟨(finiteIso F hF).some ≪≫
      Functor.isoWhiskerLeft (forget FintypeCat) (sigmaConst.mapIso e)⟩
  · intro I _ _ D c hc hs
    let F := profiniteToProEt ⋙ Scheme.ProEt.forget specZ.{u}
    have hsch : IsLimit (profiniteToScheme.mapCone c) :=
      isLimitOfPreserves Scheme.Spec (lc_limit c hc hs).some
    have : IsConnected I := IsCofiltered.isConnected I
    have hover : IsLimit (F.mapCone c) := isLimitOfReflects (Over.forget specZ) hsch
    exact ⟨isLimitOfPreserves (Over.pullback (toSpecZ X)) hover⟩
  · intro A _ S T f hf
    exact Precoverage.mem_coverings_of_isPullback
      (fun a ↦ profiniteToScheme.map (f a)) (spec_cover A S T f hf)
      (pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X)) _
      (fun a ↦ pullback.fst (toSpecZ (profiniteToScheme.obj (S a))) (toSpecZ X))
      (fun a ↦ (MorphismProperty.Over.isPullback_map_left (toSpecZ X)
        (profiniteToProEt.map (f a))).flip)
  · refine ⟨?_⟩
    have h : toSpecZ specZ.{u} = 𝟙 _ := specULiftZIsTerminal.hom_ext _ _
    exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft profiniteToProEt
      (MorphismProperty.Over.pullbackCongr h ≪≫
        MorphismProperty.Over.pullbackId _ _ _))
      (Scheme.ProEt.forget specZ ⋙ Over.forget specZ)

end AlgebraicGeometry.ProEtale
