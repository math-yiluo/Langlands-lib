/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeSourceIso
import WeilConjectures.AlgebraicGeometry.Single.SingleOpenTensorCoefficientCoherence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Identifying a relative open arrow for a single coefficient -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cancel_single_maps
    {A C : Type*} [Category A] [Category C]
    (F : A ⥤ C) {X Y : C} {U V : A} (e : X ⟶ Y) (q : Y ⟶ F.obj U) (b : U ≅ V) :
    (e ≫ q ≫ F.map b.hom) ≫ F.map b.inv = e ≫ q := by
  simp only [Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_normalize
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) :
    let := Scheme.Modules.canonicalTensorPullbackAdditive f
    Scheme.picardTermwiseSingleMap f N =
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f).app
        ((HomotopyCategory.singleFunctor _ 0).obj N) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.app N)) := by
  exact Scheme.single_map_normalize f N

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_open_iso
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (N : Y.Modules) :
    IsIso (Scheme.picardTermwiseSingleMap f N) := by
  let : HasDerivedCategory.{u + 1} X.Modules := inferInstanceAs
    (HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : HasDerivedCategory.{u + 1} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let T := Scheme.Modules.tensorPullback f
  let := Scheme.Modules.canonicalTensorPullbackAdditive f
  let η : T ≅ Scheme.Modules.restrictFunctor f :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback f).symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso η.symm
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso η.symm
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let V := HomotopyCategory.quasiIso Y.Modules (.up ℤ)
  have : (DerivedCategory.Qh (C := Y.Modules)).IsLocalization V :=
    inferInstanceAs ((DerivedCategory.Qh (C := Y.Modules)).IsLocalization
      (HomotopyCategory.quasiIso Y.Modules (.up ℤ)))
  have : (derivedPullback f).IsLeftDerivedFunctor ε V :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f
  have hInv : V.IsInvertedBy (T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso V T.mapDerivedCategoryFactorsh]
    exact MorphismProperty.IsInvertedBy.of_comp V DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh V) T.mapDerivedCategory
  have : IsIso ε :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts (derivedPullback f) ε hInv
  rw [single_normalize]
  infer_instance

/-- Restricting a single coefficient to an open contained in its domain gives the
literal tensor-pullback standard comparison, as an isomorphism of arrows.
Source: Stacks Project, Tags 08HY, 0D5S, 01JR and 0A1D.
(blueprint: lem-pc-standard-single-open-relative-arrow).

Proof: The open scheme of W inverse image Z is canonically isomorphic to Z,
with its inclusion into W identified with homOfLE hZ. On the cartesian base
changes use the projection-preserving pullback isomorphism for this scheme
isomorphism and for associating the two pullbacks. Exact open restriction
identifies derived pullback of N[0] with the single complex of the literal tensor
pullback of N; the comparison is the derived-to-ordinary pullback counit. Use
these coefficient comparisons, direct-image composition, and pullback along g
to construct the source and target vertex isomorphisms. Expand relativeMVLocalArrow
and standardSingleBaseChangeMap into their base-change mates and single-complex
counits. The composition law for picardTermwiseSingleMap, the compatibility of
source-isomorphism base-change conjugacy, and the composite-adjunction counit formula
identify the two composites. This is the commuting square defining an arrow
isomorphism; each vertex map is invertible by exact open restriction and scheme
isomorphism transport. More explicitly, put J = W inverse image Z, i:J -> W,
X' = W times_B A with projections q:X' -> W and f':X' -> A, and
J' = X' times_W J with projections r:J' -> X' and k:J' -> J. Let
P = Z times_B A. The source isomorphism e:J -> Z is isoOfLE hZ. The two
projections define e':J' -> P; the inverse is obtained by first lifting into X'
and then into J'. The projection equations and pullback extensionality prove
both inverse identities and k;e = e';(P -> Z).

Write L and R for the pinned derived functors. Let c(h,t) compare successive
pullback along t then h with pullback along h;t.
Put M = tensorPullbackObj (Y.homOfLE hZ) N. Exactness of open restriction,
followed by tensor-pullback composition, gives
alpha:L_e(M[0]) -> L_i(N[0]) as an isomorphism. On J' the same construction
and the equality r;q = k;i give an isomorphism
beta:L_e'((P -> Z tensor-pullback M)[0]) -> L_r((q tensor-pullback N)[0]).
To check the coefficient compatibility required by exists_derivedBaseChange_source_iso,
expand the local coefficient as c(k,i), transport across k;i = r;q, inverse
c(r,q), and L_r(picardTermwiseSingleMap q N). Apply the single-map composition
identity once on each path. The tensor-composition factors are precisely those
used in alpha and beta, so cancellation and naturality give that compatibility.
Apply source-isomorphism conjugacy with these alpha and beta, and invert its
arrow isomorphism to orient it from the local arrow to the standard arrow.
The vertex isomorphisms use the invertible derived adjunction units for e and e';
their inverse identities follow from the adjunction triangle identities.
No assertion about invertibility of a base-change map is used.
Empty Z or W and zero N give the same comparison between zero objects;
Z = W gives the identity-open comparison. -/
theorem standardSingle_open_relative_arrow
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B)
    (W Z : Y.Opens) (hZ : Z ≤ W) (N : W.toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let f := W.ι ≫ p
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N
    let K' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N)
    Nonempty
      (relativeMVLocalArrow f (pullback.snd f g) g (pullback.fst f g)
          (IsPullback.of_hasPullback f g) K K'
          (Scheme.picardTermwiseSingleMap (pullback.fst f g) N) (W.ι ⁻¹ᵁ Z) ≅
        Arrow.mk (standardSingleBaseChangeMap (Z.ι ≫ p)
          (Scheme.Modules.tensorPullbackObj (Y.homOfLE hZ) N) g)) := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let f := W.ι ≫ p
  let J := W.ι ⁻¹ᵁ Z
  let q := pullback.fst f g
  let f' := pullback.snd f g
  let r := pullback.fst q J.ι
  let k := pullback.snd q J.ι
  let t := pullback.fst (Z.ι ≫ p) g
  let s := pullback.snd (Z.ι ≫ p) g
  let e := Scheme.Opens.isoOfLE hZ
  have hi : e.hom ≫ Y.homOfLE hZ = J.ι := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact Scheme.Opens.isoOfLE_hom_ι hZ
  have hf : e.hom ≫ (Z.ι ≫ p) = J.ι ≫ f := by
    simp only [f, ← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, J, e]
  let e' : pullback q J.ι ≅ pullback (Z.ι ≫ p) g :=
    pullbackSymmetry q J.ι ≪≫ pullbackRightPullbackFstIso f g J.ι ≪≫
      asIso (pullback.map (J.ι ≫ f) g (Z.ι ≫ p) g e.hom (𝟙 _) (𝟙 _)
        (by simpa using hf.symm) (by simp))
  have ht : k ≫ e.hom = e'.hom ≫ t := by
    simp [e', t, k, q]
  have hf' : e'.hom ≫ s = r ≫ f' := by
    simp [e', s, r, f', q]
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N
  let K' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj q N)
  let M := Scheme.Modules.tensorPullbackObj (Y.homOfLE hZ) N
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toScheme.toRingedSpace)) 0).obj M
  let E' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback (Z.ι ≫ p) g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj t M)
  let phi0 := (relativeMVComp k J.ι).hom.app K ≫
    eqToHom (congrArg (fun a ↦ (derivedPullback a).obj K)
      (pullback.condition (f := q) (g := J.ι)).symm) ≫
    (relativeMVComp r q).inv.app K ≫
    (derivedPullback r).map (Scheme.picardTermwiseSingleMap q N)
  have : IsOpenImmersion J.ι := inferInstance
  have : IsIso (Scheme.picardTermwiseSingleMap J.ι N) := single_open_iso J.ι N
  have : IsIso (Scheme.picardTermwiseSingleMap e.hom M) := single_open_iso e.hom M
  have : IsIso (Scheme.picardTermwiseSingleMap r
      (Scheme.Modules.tensorPullbackObj q N)) := single_open_iso r _
  have : IsIso (Scheme.picardTermwiseSingleMap e'.hom
      (Scheme.Modules.tensorPullbackObj t M)) := single_open_iso e'.hom _
  let aN := (Scheme.Modules.tensorPullbackCompositionIso
    e.hom (Y.homOfLE hZ) J.ι hi).symm.app N
  have heq : (e'.hom ≫ t) ≫ Y.homOfLE hZ = r ≫ q := by
    rw [← ht, Category.assoc, hi]
    exact (pullback.condition (f := q) (g := J.ι)).symm
  let bN := (Scheme.Modules.tensorPullbackCompositionIso
      e'.hom t (e'.hom ≫ t) rfl).symm.app M ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso
      (e'.hom ≫ t) (Y.homOfLE hZ) (r ≫ q) heq).symm.app N ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).app N
  let alpha : (derivedPullback e.hom).obj E ≅ (derivedPullback J.ι).obj K :=
    asIso (Scheme.picardTermwiseSingleMap e.hom M) ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings J.toScheme.toRingedSpace)) 0).mapIso aN ≪≫
      (asIso (Scheme.picardTermwiseSingleMap J.ι N)).symm
  let beta : (derivedPullback e'.hom).obj E' ≅ (derivedPullback r).obj K' :=
    asIso (Scheme.picardTermwiseSingleMap e'.hom (Scheme.Modules.tensorPullbackObj t M)) ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback q J.ι).toRingedSpace)) 0).mapIso bN ≪≫
      (asIso (Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N))).symm
  have ha : alpha.hom ≫ Scheme.picardTermwiseSingleMap J.ι N =
      Scheme.picardTermwiseSingleMap e.hom M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings J.toScheme.toRingedSpace)) 0).map aN.hom := by
    simp [alpha]
  have hb : beta.hom ≫
      Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N) =
      Scheme.picardTermwiseSingleMap e'.hom (Scheme.Modules.tensorPullbackObj t M) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback q J.ι).toRingedSpace)) 0).map bN.hom := by
    simp [beta]
  have hphi := single_open_tensor_coefficient_coherence
    (Y.homOfLE hZ) q t J.ι r k e e' hi ht
    (pullback.condition (f := q) (g := J.ι)).symm N
    inferInstance alpha.hom beta.hom ha hb
  have h0 : k ≫ (e.hom ≫ (Z.ι ≫ p)) = (e'.hom ≫ s) ≫ g := by
    rw [← Category.assoc, ht, Category.assoc, pullback.condition, ← Category.assoc]
  have transport := exists_derivedBaseChange_source_iso
    (Z.ι ≫ p) s g t pullback.condition e e' k ht h0 E E'
    ((derivedPullback J.ι).obj K) ((derivedPullback r).obj K')
    (Scheme.picardTermwiseSingleMap t M) phi0 alpha beta hphi
  revert transport h0
  rw [hf, hf']
  intro h0 transport
  obtain ⟨a, b, hab⟩ := transport
  exact ⟨(Arrow.isoMk a b hab.symm).symm⟩

end AlgebraicGeometry
