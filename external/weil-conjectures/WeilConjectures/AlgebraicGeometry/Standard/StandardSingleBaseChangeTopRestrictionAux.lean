/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.Derived.DerivedBaseChangeSourceTransport
import WeilConjectures.AlgebraicGeometry.Open.OpenSingleCoefficientTransport

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The derived pullback unit for a scheme isomorphism is invertible.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-standard-single-base-change-top-restriction-iso-pullback-unit) -/
theorem standardSingleBaseChange_topRestriction_iso_pullback_unit
    [∀ X : Scheme.{u},
      HasDerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Z : Scheme.{u}} (s : X ≅ Z) :
    IsIso (relativeMVAdj s.hom).unit := by
  obtain ⟨_, i, _, _, _⟩ := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))
  let b : derivedPullback s.hom ⋙ derivedPullback s.inv ≅ 𝟭 _ :=
    relativeMVComp s.inv s.hom ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) s.inv_hom_id) ≪≫ i Z
  let c : derivedPullback s.inv ⋙ derivedPullback s.hom ≅ 𝟭 _ :=
    relativeMVComp s.hom s.inv ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) s.hom_inv_id) ≪≫ i X
  have : (derivedPullback s.inv).Faithful := Functor.Faithful.of_comp_iso c
  have : (derivedPullback s.hom).Faithful := Functor.Faithful.of_comp_iso b
  have : (derivedPullback s.hom).Full := Functor.Full.of_comp_faithful_iso b
  infer_instance

set_option linter.unusedVariables false in
/-- Canonical source restriction comparison for the top open.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: def-pc-standard-single-base-change-top-restriction-source-iso) -/
noncomputable def standardSingleBaseChange_topRestriction_sourceIso
    {Y B : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι)) := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let j := (⊤ : Y.Opens).ι
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  have : IsIso (relativeMVAdj j).unit :=
    standardSingleBaseChange_topRestriction_iso_pullback_unit Y.topIso
  let a : (derivedPullback j).obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj (M.restrict j) :=
    (singleComplexOpenPullbackIso Y ⊤).app K ≪≫
      ((schemeOpenRestriction Y ⊤).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings
          (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).mapIso
        ((Scheme.Modules.overFunctorEquiv ⊤).app M)
  exact (schemeDerivedDirectImage p).mapIso
      (asIso ((relativeMVAdj j).unit.app K)) ≪≫
    (relativeMVImageComp j p).app ((derivedPullback j).obj K) ≪≫
    (schemeDerivedDirectImage (j ≫ p)).mapIso a

set_option linter.unusedVariables false in
/-- Compatibility equation for the canonical source restriction comparison.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-standard-single-base-change-top-restriction-compatibility)

Proof: Substitute the hypothesis on `e`. Write L_f = derivedPullback f and
R_f = schemeDerivedDirectImage f; composition of arrows below is written `≫`.
Put j = (⊤ : Y.Opens).ι, N = M.restrict j, K = M[0], K' = N[0]. Let
P = pullback p g have projections r = pullback.fst p g and s = pullback.snd p g.
Let P' = pullback (j ≫ p) g have projections r' and s'. The universal property
constructs k : P' ≅ P with k.hom ≫ r = r' ≫ j and k.hom ≫ s = s': its forward
map is pullback.lift (r' ≫ j) s', and its inverse is pullback.lift (r ≫ j.inv) s.
Here j.inv denotes Y.topIso.inv. Pullback projection extensionality and the two
inverse identities for Y.topIso prove that these maps are inverse.

Let a : L_j K ≅ K' be precisely the single restriction comparison in sourceIso.
For any f write q_f(V) = Scheme.picardTermwiseSingleMap f V. Tensor pullback
along the isomorphism k.hom is exact, so q_k on any module is invertible.
The canonical module isomorphism b from tensorPullbackObj k.hom
(tensorPullbackObj r M) to tensorPullbackObj r' N is obtained by tensor-pullback
composition along k.hom,r, transport across k.hom ≫ r = r' ≫ j, inverse
composition along r',j, and tensorPullback r' of the canonical comparison
from tensorPullbackObj j M to N. More explicitly, put
δ(h,f) = Scheme.Modules.tensorPullbackCompositionIso h f (h ≫ f) rfl, directed from tensor pullback
of h ≫ f to tensor pullback
along f followed by h. If ρ : tensorPullbackObj j M ≅ N is the canonical
adjoint-uniqueness comparison to restriction used in a, then
  b = δ(k.hom,r).inv.app M ≫ transport ≫ δ(r',j).hom.app M
    ≫ (Scheme.Modules.tensorPullback r').map ρ.hom,
where transport is along k.hom ≫ r = r' ≫ j. Thus a.hom is q_j(M) followed
by single.map ρ.hom. All these comparisons are pinned to the
same tensor-pullback adjunctions. Define
  T = (tensorPullbackObj r M)[0], T' = (tensorPullbackObj r' N)[0],
  d : L_k T ≅ T' = asIso(q_k(tensorPullbackObj r M)) ≪≫ single.mapIso b.
Write C(h,f) for relativeMVComp h f, including equality transport when paths
are identified. The coefficient-composition identity is
  L_k(q_r(M)) ≫ d.hom =
    C(k,r).hom.app K ≫ C(r',j).inv.app K ≫ L_r'(a.hom) ≫ q_r'(N).
The equality transport between the two C components uses k.hom ≫ r = r' ≫ j.
To verify this identity, apply Scheme.picardTermwiseSingleMap_composition to
(k.hom,r) and (r',j). Its tensorPullbackCompositionIso and single-complex
comparison factors are exactly those defining b. Cancel the inverse factors,
and use naturality of the single comparison for the tensor-to-restriction map.
The defining leftDerivedLift factorization in exists_derivedPullbackComposition
ensures that these are the pinned C comparisons, rather than arbitrary ones.

Define F : R_s T ≅ R_s' T' by composing R_s of the invertible unit
T ≅ R_k L_k T, (relativeMVImageComp k.hom s).app (L_k T), transport across
k.hom ≫ s = s', and R_s'.mapIso d. Invertibility of the unit follows from
standardSingleBaseChange_topRestriction_iso_pullback_unit k. Set t = F.symm.

Here is the compatibility calculation before cancelling F. Put D = L_g R_p K.
Write B(r,s,p;K) for the transpose of schemeDerivedBaseChangeMap p s g r:
  B(r,s,p;K) = C(s,g).hom.app (R_p K) ≫ C(r,p).inv.app (R_p K)
    ≫ L_r((relativeMVAdj p).counit.app K),
with the pullback.condition transport between the two C components. Thus the
transpose of standardSingleBaseChangeMap p M g under relativeMVAdj s is
B(r,s,p;K) ≫ q_r(M). Under relativeMVAdj s', the transpose of that map followed
by F.hom is
  C(k,s).inv.app D ≫ L_k(B(r,s,p;K)) ≫ L_k(q_r(M)) ≫ d.hom.
This follows by expanding F and the right-adjoint mate relativeMVImageComp:
its mate formula converts the composite adjunction to relativeMVAdj s', and
L_k of the unit followed by the k counit cancels by the left triangle identity.

Substitute the coefficient identity. The remaining prefix satisfies
  C(k,s).inv.app D ≫ L_k(B(r,s,p;K)) ≫ C(k,r).hom.app K
    ≫ C(r',j).inv.app K ≫ L_r'(a.hom)
  = L_s'(L_g(e.hom)) ≫ B(r',s',j ≫ p;K').
For this equation, expand e as R_p(unit_j) followed by relativeMVImageComp j p
and R_(j≫p)(a). Move a through the counit by counit naturality. Expand the
composition counit using the right-adjoint mate defining relativeMVImageComp:
the counit for j ≫ p is C(j,p).inv followed by L_j of the p counit and then
the j counit (with the right-adjoint comparison on its source). Naturality moves
the inserted unit_j next to the j counit, where
  L_j(unit_j.app K) ≫ counit_j.app (L_j K) = 𝟙 (L_j K)
cancels it. The other mate cancellation is
  unit_j.app (R_j V) ≫ R_j(counit_j.app V) = 𝟙 (R_j V).
Associativity and the identity laws in exists_derivedPullbackComposition
identify the remaining C paths using r ≫ p = s ≫ g, r' ≫ j ≫ p = s' ≫ g,
and the two projection identities for k. These are the pinned composition
laws, the single-map composition identity, and the two adjunction triangle
identities; no comparison along g is inverted.

Appending q_r'(N) shows equality of the two transposes under relativeMVAdj s'.
The adjunction hom equivalence is injective, hence
  standardSingleBaseChangeMap p M g ≫ F.hom =
    L_g(e.hom) ≫ standardSingleBaseChangeMap (j ≫ p) N g.
Compose on the right with F.inv and cancel F.hom ≫ F.inv to get the claimed
equation with t = F.symm. All constructions are functorial and remain valid
for empty schemes and zero modules. -/
theorem standardSingleBaseChange_topRestriction_compatibility
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∀ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι))),
      e = standardSingleBaseChange_topRestriction_sourceIso p M → ∃ (t : (schemeDerivedDirectImage
          (pullback.snd ((⊤ : Y.Opens).ι ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj
              (pullback.fst ((⊤ : Y.Opens).ι ≫ p) g)
              (M.restrict (⊤ : Y.Opens).ι))) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap ((⊤ : Y.Opens).ι ≫ p)
            (M.restrict (⊤ : Y.Opens).ι) g ≫ t.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  intro e he
  subst e
  let j := (⊤ : Y.Opens).ι
  let N := M.restrict j
  let r := pullback.fst p g
  let s := pullback.snd p g
  let r' := pullback.fst (j ≫ p) g
  let s' := pullback.snd (j ≫ p) g
  have h : r ≫ p = s ≫ g := pullback.condition
  have h' : r' ≫ (j ≫ p) = s' ≫ g := pullback.condition
  let kh : pullback (j ≫ p) g ⟶ pullback p g :=
    pullback.lift (r' ≫ j) s' (by simpa only [Category.assoc] using h')
  let ki : pullback p g ⟶ pullback (j ≫ p) g :=
    pullback.lift (r ≫ Y.topIso.inv) s (by
      change r ≫ Y.topIso.inv ≫ Y.topIso.hom ≫ p = s ≫ g
      simpa only [Iso.inv_hom_id_assoc] using h)
  let k : pullback (j ≫ p) g ≅ pullback p g :=
    { hom := kh
      inv := ki
      hom_inv_id := by
        apply pullback.hom_ext <;>
          simp [kh, ki, r, s, r', s', j, Category.assoc]
      inv_hom_id := by
        apply pullback.hom_ext <;>
          simp [kh, ki, r, s, r', s', j, Category.assoc] }
  have hr : k.hom ≫ r = r' ≫ j := pullback.lift_fst _ _ _
  have hs : k.hom ≫ s = s' := pullback.lift_snd _ _ _
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  let K' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).obj N
  let T := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj r M)
  let T' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback (j ≫ p) g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj r' N)
  let a : (derivedPullback j).obj K ≅ K' :=
    (singleComplexOpenPullbackIso Y ⊤).app K ≪≫
      ((schemeOpenRestriction Y ⊤).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings
          (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).mapIso
        ((Scheme.Modules.overFunctorEquiv ⊤).app M)
  obtain ⟨d, hd⟩ := exists_openSingle_coefficient_transport ⊤ M r r' k hr
  have : IsIso (relativeMVAdj k.hom).unit :=
    standardSingleBaseChange_topRestriction_iso_pullback_unit k
  let F : (schemeDerivedDirectImage s).obj T ≅
      (schemeDerivedDirectImage s').obj T' :=
    (schemeDerivedDirectImage s).mapIso (asIso ((relativeMVAdj k.hom).unit.app T)) ≪≫
      (relativeMVImageComp k.hom s).app ((derivedPullback k.hom).obj T) ≪≫
      eqToIso (congrArg (fun f ↦ (schemeDerivedDirectImage f).obj
        ((derivedPullback k.hom).obj T)) hs) ≪≫
      (schemeDerivedDirectImage s').mapIso d
  refine ⟨F.symm, ?_⟩
  have hc := derivedBaseChange_source_transport p g j r s r' s' k.hom h h' hr hs
    K K' T T' a.hom (Scheme.picardTermwiseSingleMap r M)
      (Scheme.picardTermwiseSingleMap r' N) d.hom hd
  have hc' : standardSingleBaseChangeMap p M g ≫ F.hom =
      (derivedPullback g).map
        (standardSingleBaseChange_topRestriction_sourceIso p M).hom ≫
          standardSingleBaseChangeMap (j ≫ p) N g := by
    simpa only [standardSingleBaseChangeMap,
      standardSingleBaseChange_topRestriction_sourceIso, F, a, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, asIso_hom, eqToIso.hom, Category.assoc] using hc
  have hh := congrArg (fun f ↦ f ≫ F.inv) hc'
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.symm_hom] using hh

end AlgebraicGeometry
