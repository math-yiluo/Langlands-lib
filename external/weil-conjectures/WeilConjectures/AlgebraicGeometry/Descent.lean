/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.Modules.DescentEffective
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.Modules.FpqcFullyFaithful
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent

/-!
# Fpqc descent for quasi-coherent modules and for finite locally free closed subschemes

Let `{T i ⟶ T}` be an fpqc covering, i.e. a family of arrows generating a covering sieve
for `AlgebraicGeometry.Scheme.fpqcTopology`. This file states the two descent theorems
needed for the construction of the Picard scheme.

**(D1) Descending modules.** Descent data for quasi-coherent modules relative to the
covering are effectively represented by quasi-coherent modules on `T`: the comparison
functor from `T.Modules` to descent data is fully faithful on quasi-coherent objects, and
every descent datum with quasi-coherent components comes from a quasi-coherent module.
The equivalence preserves finite presentability and local freeness, and in particular
invertible modules glue to an invertible module.

**(D2) Effective closed immersions.** Given `X ⟶ T` and closed subschemes of the base
changes `X ×_T T i` which are finite locally free of degree `d` over `T i` and agree after
further base change, there is a unique closed subscheme of `X` restricting to them, and it
is finite locally free of degree `d` over `T`.

## Implementation notes

Closed subschemes are spelled as ideal sheaves (`AlgebraicGeometry.Scheme.IdealSheafData`),
which is what makes the cocycle condition of the blueprint degenerate to a plain equality:
`IdealSheafData` is a *set*, so descent data for it carry no extra structure and (D2) is a
genuine sheaf condition. Degrees are measured by `AlgebraicGeometry.Scheme.Hom.finrank`.

(D1) is stated as five separate assertions rather than through
`CategoryTheory.Functor.IsStack`: `Mathlib.CategoryTheory.Sites.Descent.IsStack` asks for
effectivity of *all* descent data, whereas what holds here is effectivity of the
quasi-coherent ones, which is not an instance of that class.

Flatness of a sheaf of modules has no name in Mathlib yet, so its preservation under the
equivalence of (D1) is not part of the statements below.

Local freeness is only claimed to descend for modules of finite presentation: a module which is
locally free of infinite rank after a faithfully flat base change need not be locally free. A
module of finite presentation which becomes locally free after such a base change is flat and
of finite presentation, hence finite locally free.

## Main statements

- `AlgebraicGeometry.bijective_toDescentData_map_of_mem_fpqcTopology`,
  `AlgebraicGeometry.exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology`,
  `AlgebraicGeometry.isFinitePresentation_of_toDescentData_iso`,
  `AlgebraicGeometry.isLocallyFree_of_toDescentData_iso`,
  `AlgebraicGeometry.isFiniteLocallyFreeOfRank_of_toDescentData_iso` and
  `AlgebraicGeometry.isInvertible_of_toDescentData_iso`: (D1), fpqc descent for
  quasi-coherent modules. Effectivity and the rank statement are deduced from
  `AlgebraicGeometry.exists_toDescentData_iso`,
  `AlgebraicGeometry.isQuasicoherent_of_toDescentData_iso_of_mem_fpqcTopology` and
  `AlgebraicGeometry.isFiniteLocallyFreeOfRank_of_toDescentData_iso_of_isQuasicoherent`.
- `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_mem_fpqcTopology` and
  `AlgebraicGeometry.Scheme.IdealSheafData.eq_of_comap_eq_of_mem_fpqcTopology`: closed
  subschemes satisfy fpqc descent.
- `AlgebraicGeometry.isSheaf_fpqc_finiteLocallyFreeSubscheme`: (D2), the sheaf condition
  for closed subschemes which are finite locally free of a fixed degree.

## Proofs

Invertibility descends because an invertible module is the same as a finite locally free
module of rank one. (D2) follows the blueprint: the closed subschemes glue to a closed
subscheme `Z ⊆ X`, unique because pulling back ideal sheaves along an fpqc covering is
injective, and `Z ⟶ T` is finite, flat and of finite presentation because these properties
descend along fpqc coverings
(`AlgebraicGeometry.Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`); the degree is read
off on the covering.

The gluing of the closed subschemes does not go through (D1): where the blueprint descends the
quotient modules `𝒪 / I i`, we write down the descended ideal sheaf directly. Over an affine
open of `X` the covering is refined by finitely many flat morphisms `f j : W j ⟶ U` from affine
schemes, and `⨅ j, (I j).map (f j)` restricts to the `I j` by flat base change for ideal sheaves
and because flat pullback commutes with finite intersections; the local ideal sheaves so
obtained are unique, hence glue.
-/

@[expose] public section

universe w u

open CategoryTheory Opposite CategoryTheory.Bicategory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {ι : Type w} {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T)

/-- **Finite presentation descends along an fpqc covering.**

(blueprint: `lemma-rigidification-along-section--1`; `det-thm-picard-descent`, part (D1)) -/
theorem isFinitePresentation_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFinitePresentation) :
    (M : T.Modules).IsFinitePresentation :=
  isFinitePresentation_of_toDescentData_iso_of_isQuasicoherent g hg D M
    (isQuasicoherent_of_toDescentData_iso_of_mem_fpqcTopology g hg D M hM
      fun i ↦ have := hD i; inferInstance) hM hD

/-- **Finite local freeness descends along an fpqc covering.** A descent datum whose
components are of finite presentation and locally free, i.e. finite locally free with a rank
allowed to vary locally, comes from a module on `T` which is locally free; it is of finite
presentation by `isFinitePresentation_of_toDescentData_iso`.

(blueprint: `lemma-rigidification-along-section--1`; `det-thm-picard-descent`, part (D1)) -/
theorem isLocallyFree_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFinitePresentation ∧
      (D.obj i : (T' i).Modules).IsLocallyFree) :
    (M : T.Modules).IsLocallyFree :=
  isLocallyFree_of_toDescentData_iso_of_isQuasicoherent g hg D M
    (isQuasicoherent_of_toDescentData_iso_of_mem_fpqcTopology g hg D M hM
      fun i ↦ have := (hD i).1; inferInstance)
    hM hD

/-- **Fpqc descent for modules: existence.** For an fpqc covering `{g i : T i ⟶ T}`, every
descent datum whose components are quasi-coherent comes from a sheaf of modules on `T`.

(blueprint: `lemma-rigidification-along-section--1`; `det-thm-picard-descent`, part (D1)) -/
theorem exists_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsQuasicoherent) :
    ∃ M : modulesPseudofunctor.obj (.mk (op T)),
      Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D) :=
  have ⟨M, _, hM⟩ := exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology g hg D hD
  ⟨M, hM⟩

namespace Scheme.Modules

/-- **Finite local freeness of rank `r` descends along a faithfully flat map of affine schemes**
`Spec.map φ : Spec B ⟶ Spec R`, for quasi-coherent modules: the global sections of the pullback
are `B ⊗[R] Γ(P, ⊤)`, and finite presentation, flatness and rank descend along `R ⟶ B`. -/
theorem isFiniteLocallyFreeOfRank_of_pullback_Spec_map {R B : CommRingCat.{u}} (φ : R ⟶ B)
    [Flat (Spec.map φ)] [Surjective (Spec.map φ)] (P : (Spec R).Modules) [P.IsQuasicoherent]
    {r : ℕ} [((pullback (Spec.map φ)).obj P).IsFiniteLocallyFreeOfRank r] :
    P.IsFiniteLocallyFreeOfRank r := by
  obtain ⟨_, _, hrank⟩ := rankAtStalk_eq_of_isFiniteLocallyFreeOfRank
    ((pullback (Spec.map φ)).obj P) (r := r)
  have hφ : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨‹_›, ‹_›⟩
  let e := pullbackSpecΓEquiv φ P
  have hfp : Module.FinitePresentation B
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) := .of_equiv e.symm
  have hfl : Module.Flat B
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) := .of_linearEquiv e
  have hrank' (q : PrimeSpectrum B) : Module.rankAtStalk
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) q = r := by
    rw [Module.rankAtStalk_eq_of_equiv e, hrank]
  algebraize [φ.hom]
  have : Module.FinitePresentation B (TensorProduct R B Γ(P, ⊤)) := by exact hfp
  have : Module.Flat B (TensorProduct R B Γ(P, ⊤)) := by exact hfl
  have : Module.FinitePresentation R Γ(P, ⊤) :=
    .of_finitePresentation_tensorProduct_of_faithfullyFlat (B := B)
  have : Module.Flat R Γ(P, ⊤) := .of_flat_tensorProduct _ _ B
  exact isFiniteLocallyFreeOfRank_of_rankAtStalk_eq P
    (Module.rankAtStalk_eq_of_rankAtStalk_tensorProduct_eq (B := B) hrank')

/-- **Finite local freeness of rank `r` descends along a flat surjective morphism**
`F : W ⟶ Spec R` from an affine scheme, for quasi-coherent modules on `Spec R`. -/
theorem isFiniteLocallyFreeOfRank_of_pullback_of_isAffine {R : CommRingCat.{u}} {W : Scheme.{u}}
    [IsAffine W] (F : W ⟶ Spec R) [Flat F] [Surjective F] (P : (Spec R).Modules)
    [P.IsQuasicoherent] {r : ℕ} [((pullback F).obj P).IsFiniteLocallyFreeOfRank r] :
    P.IsFiniteLocallyFreeOfRank r := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ F)
  have : Flat (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Surjective (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : ((pullback (Spec.map φ)).obj P).IsFiniteLocallyFreeOfRank r :=
    .of_iso (pullbackCompOfEq W.isoSpec.inv F _ hφ.symm P)
  exact isFiniteLocallyFreeOfRank_of_pullback_Spec_map φ P

/-- **Finite local freeness of rank `r` descends along a finite jointly surjective family of
flat morphisms** `f j : W j ⟶ Spec R` from affine schemes, for quasi-coherent modules on
`Spec R`: the morphism `∐ W j ⟶ Spec R` is flat and surjective, with affine source. -/
theorem isFiniteLocallyFreeOfRank_of_pullback_of_iUnion_range_eq_univ {R : CommRingCat.{u}}
    (P : (Spec R).Modules) [P.IsQuasicoherent] {κ : Type u} [Finite κ] {W : κ → Scheme.{u}}
    [∀ j, IsAffine (W j)] (f : ∀ j, W j ⟶ Spec R) [∀ j, Flat (f j)]
    (hf : ⋃ j, Set.range (f j) = Set.univ) {r : ℕ}
    (h : ∀ j, ((pullback (f j)).obj P).IsFiniteLocallyFreeOfRank r) :
    P.IsFiniteLocallyFreeOfRank r := by
  have : Surjective (Sigma.desc f) := .sigmaDesc_of_union_range_eq_univ hf
  have : ((pullback (Sigma.desc f)).obj P).IsFiniteLocallyFreeOfRank r := by
    refine isFiniteLocallyFreeOfRank_of_isOpenImmersion _ (Sigma.ι W)
      (sigmaOpenCover W).iSup_opensRange fun j ↦ ?_
    have := h j
    exact .of_iso (pullbackCompOfEq _ _ _ (Sigma.ι_comp_desc f j) P).symm
  exact isFiniteLocallyFreeOfRank_of_pullback_of_isAffine (Sigma.desc f) P

end Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine-local step of `isFiniteLocallyFreeOfRank_of_toDescentData_iso_of_isQuasicoherent`:
the pullback of `M` to the spectrum of the ring of sections of an affine open is finite locally
free of rank `r`. The covering is refined over `U` by finitely many flat affine schemes; their
disjoint union is the spectrum of a faithfully flat `Γ(T, U)`-algebra `B`, over which the
global sections of `M` become finite locally free of rank `r`, and finite presentation, flatness
and rank descend along `Γ(T, U) → B`. -/
theorem isFiniteLocallyFreeOfRank_pullback_fromSpec_of_toDescentData_iso
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T))) (hMq : (M : T.Modules).IsQuasicoherent)
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D)) (r : ℕ)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFiniteLocallyFreeOfRank r)
    {U : T.Opens} (hU : IsAffineOpen U) :
    ((Scheme.Modules.pullback hU.fromSpec).obj M).IsFiniteLocallyFreeOfRank r := by
  obtain ⟨e⟩ := hM
  obtain ⟨κ, W, f, _, _, _, hfS, hcov⟩ := Scheme.exists_finite_affine_flat_of_mem_fpqcTopology
    (Scheme.fpqcTopology.pullback_stable hU.fromSpec hg)
  choose i k hk using fun j ↦ (Sieve.mem_ofArrows_iff _ _ _).1 (hfS j)
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_pullback_of_iUnion_range_eq_univ _ f ?_
    fun j ↦ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨Y, h, hh, y, rfl⟩ := Scheme.exists_mem_of_mem_fpqcTopology hcov x
    obtain ⟨j, k', rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
    exact Set.mem_iUnion.2 ⟨j, k' y, rfl⟩
  · -- `f j ≫ fromSpec = k j ≫ g (i j)`, and `(g (i j))^* M ≅ D (i j)` by the descent datum
    have := hD (i j)
    let c : (Scheme.Modules.pullback (g (i j))).obj M ≅ D.obj (i j) :=
      ⟨e.hom.hom (i j), e.inv.hom (i j), congrArg (fun φ ↦ φ.hom (i j)) e.hom_inv_id,
        congrArg (fun φ ↦ φ.hom (i j)) e.inv_hom_id⟩
    exact .of_iso ((Scheme.Modules.pullback (k j)).mapIso c.symm ≪≫
      pullbackCompOfEq (k j) (g (i j)) _ rfl M ≪≫
      (pullbackCompOfEq (f j) hU.fromSpec _ (hk j) M).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Finite local freeness of a fixed rank descends along an fpqc covering**, for a
quasi-coherent module: this is part (2) of the blueprint lemma, which is stated for
quasi-coherent modules.

(blueprint: `lemma-rigidification-along-section--1`; `det-thm-picard-descent`, part (D1)) -/
theorem isFiniteLocallyFreeOfRank_of_toDescentData_iso_of_isQuasicoherent
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T))) (hMq : (M : T.Modules).IsQuasicoherent)
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D)) (r : ℕ)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFiniteLocallyFreeOfRank r) :
    (M : T.Modules).IsFiniteLocallyFreeOfRank r := by
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_isOpenImmersion (M : T.Modules)
    (fun U : T.affineOpens ↦ U.2.fromSpec) ?_ fun U ↦
      isFiniteLocallyFreeOfRank_pullback_fromSpec_of_toDescentData_iso g hg D M hMq hM r hD U.2
  simpa only [IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top T

set_option backward.isDefEq.respectTransparency.types false in
/-- **Finite local freeness of a fixed rank descends along an fpqc covering.** A descent datum
whose components are finite locally free of rank `r` comes from a module on `T` which is
finite locally free of rank `r`. This refines `isLocallyFree_of_toDescentData_iso`: the rank
of a finite locally free module is locally constant, and can be read off after a faithfully
flat base change.

(blueprint: `lemma-rigidification-along-section--1`; `det-thm-picard-descent`, part (D1)) -/
theorem isFiniteLocallyFreeOfRank_of_toDescentData_iso
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D)) (r : ℕ)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFiniteLocallyFreeOfRank r) :
    (M : T.Modules).IsFiniteLocallyFreeOfRank r :=
  have : (M : T.Modules).IsQuasicoherent :=
    isQuasicoherent_of_toDescentData_iso_of_mem_fpqcTopology g hg D M hM
      fun i ↦ haveI := hD i
      haveI := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree (D.obj i : (T' i).Modules) r
      inferInstance
  isFiniteLocallyFreeOfRank_of_toDescentData_iso_of_isQuasicoherent g hg D M this hM r hD

/-- **Invertibility descends along an fpqc covering**: a compatible family of invertible
modules `ℒ i` on the `T i` glues to an invertible module `ℒ` on `T` with `ℒ|_{T i} ≅ ℒ i`.

(blueprint: `lemma-rigidification-along-section--1`; `det-thm-picard-descent`, part (D1)) -/
theorem isInvertible_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsInvertible) :
    (M : T.Modules).IsInvertible :=
  (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M : T.Modules)).mpr <|
    isFiniteLocallyFreeOfRank_of_toDescentData_iso g hg D M hM 1 fun i ↦
      (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
        (D.obj i : (T' i).Modules)).mp (hD i)

namespace Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency.types false in
/-- An ideal sheaf whose pullback along every member of an fpqc covering sieve vanishes, vanishes:
the inclusion of the closed subscheme it cuts out becomes an isomorphism after base change along
the covering, hence is an isomorphism. -/
theorem eq_bot_of_comap_eq_bot_of_mem_fpqcTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ Scheme.fpqcTopology X) (K : X.IdealSheafData)
    (hK : ∀ ⦃Y : Scheme.{u}⦄ (h : Y ⟶ X), S h → K.comap h = ⊥) : K = ⊥ := by
  rw [← isIso_subschemeι_iff_eq_bot]
  refine Scheme.of_isPullback_of_mem_fpqcTopology (P := MorphismProperty.isomorphisms Scheme)
    hS K.subschemeι fun Y W h a b hh hab ↦ ?_
  have : IsIso (K.comap h).subschemeι := by
    rw [isIso_subschemeι_iff_eq_bot]
    exact hK h hh
  have : IsIso (pullback.fst h K.subschemeι) := by
    rw [← comapIso_inv_subschemeι]
    infer_instance
  change IsIso b
  rw [← hab.flip.isoPullback_hom_fst]
  infer_instance

/-- **Fpqc descent for closed subschemes: uniqueness**, for a covering sieve. Two ideal sheaves
on `X` whose pullbacks along every member of an fpqc covering sieve agree are equal. -/
theorem eq_of_forall_comap_eq_of_mem_fpqcTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ Scheme.fpqcTopology X) {J J' : X.IdealSheafData}
    (h : ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), S f → J.comap f = J'.comap f) : J = J' := by
  suffices H : ∀ J J' : X.IdealSheafData,
      (∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), S f → J.comap f = J'.comap f) → J' ≤ J from
    le_antisymm (H J' J fun _ f hf ↦ (h f hf).symm) (H J J' h)
  intro J J' h
  rw [← J.ker_subschemeι]
  refine le_ker_of_comap_eq_bot _ (eq_bot_of_comap_eq_bot_of_mem_fpqcTopology
    (Scheme.fpqcTopology.pullback_stable J.subschemeι hS) _ fun Y k hk ↦ ?_)
  rw [← comap_comp, ← h _ hk, comap_comp, comap_subschemeι, comap_bot]

/-- **Fpqc descent for closed subschemes: uniqueness.** Two ideal sheaves on `X` whose pullbacks
along every member of an fpqc covering family agree are equal.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem eq_of_comap_eq_of_mem_fpqcTopology {X : Scheme.{u}} {X' : ι → Scheme.{u}}
    (p : ∀ i, X' i ⟶ X) (hp : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X)
    {J J' : X.IdealSheafData} (h : ∀ i, J.comap (p i) = J'.comap (p i)) : J = J' := by
  refine eq_of_forall_comap_eq_of_mem_fpqcTopology hp fun Y f hf ↦ ?_
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff ..).mp hf
  rw [comap_comp, comap_comp, h i]

/-- **Fpqc descent for closed subschemes: existence.** Let `{p i : X' i ⟶ X}` be an fpqc
covering and let `I i` be ideal sheaves on the `X' i` whose pullbacks agree on every scheme
mapping compatibly to two members of the covering. Then the `I i` are the pullbacks of a single
ideal sheaf on `X`.

This is the step "descending the quotients" of the proof of
`theorem-hilbert-schemes-points-smooth-curve--1`. Over an affine open `U` of `X` the covering is
refined by finitely many flat morphisms `f j : W j ⟶ U` from affine schemes, and the ideal sheaf
`⨅ j, (I j).map (f j)` on `U` restricts to the given ones by flat base change
(`Scheme.IdealSheafData.comap_iInf_map_of_flat`); these local ideal sheaves are unique, hence
glue (`Scheme.IdealSheafData.exists_comap_ι_eq`).

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem exists_comap_eq_of_mem_fpqcTopology {X : Scheme.{u}} {X' : ι → Scheme.{u}}
    (p : ∀ i, X' i ⟶ X) (hp : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X)
    (I : ∀ i, (X' i).IdealSheafData)
    (hcompat : ∀ ⦃Y : Scheme.{u}⦄ ⦃i j : ι⦄ (a : Y ⟶ X' i) (b : Y ⟶ X' j),
      a ≫ p i = b ≫ p j → (I i).comap a = (I j).comap b) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (p i) = I i := by
  -- `K` is compatible with the `I i` along `v : V ⟶ X`
  let Good (V : Scheme.{u}) (v : V ⟶ X) (K : V.IdealSheafData) : Prop :=
    ∀ ⦃Y : Scheme.{u}⦄ (h : Y ⟶ V) (i : ι) (a : Y ⟶ X' i), h ≫ v = a ≫ p i →
      K.comap h = (I i).comap a
  have huniq {V : Scheme.{u}} (v : V ⟶ X) {K K' : V.IdealSheafData} (hK : Good V v K)
      (hK' : Good V v K') : K = K' := by
    refine eq_of_forall_comap_eq_of_mem_fpqcTopology
      (Scheme.fpqcTopology.pullback_stable v hp) fun Y h hh ↦ ?_
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff ..).mp hh
    rw [hK h i a ha, hK' h i a ha]
  have hcomap {V : Scheme.{u}} (v : V ⟶ X) {K : V.IdealSheafData} (hK : Good V v K)
      {W : Scheme.{u}} (w : W ⟶ V) : Good W (w ≫ v) (K.comap w) := by
    intro Y h i a ha
    rw [← comap_comp]
    exact hK _ i a (by rw [Category.assoc, ha])
  -- the affine case
  have hex (V : Scheme.{u}) [IsAffine V] (v : V ⟶ X) : ∃ K, Good V v K := by
    obtain ⟨κ, W, f, _, _, _, hS, hcov⟩ := Scheme.exists_finite_affine_flat_of_mem_fpqcTopology
      (Scheme.fpqcTopology.pullback_stable v hp)
    choose i a ha using fun j ↦ (Sieve.mem_ofArrows_iff ..).mp (hS j)
    let K := ⨅ j, ((I (i j)).comap (a j)).map (f j)
    have hKf (l : κ) : K.comap (f l) = (I (i l)).comap (a l) := by
      refine comap_iInf_map_of_flat f _ (fun k l ↦ ?_) l
      rw [← comap_comp, ← comap_comp]
      apply hcompat
      rw [Category.assoc, Category.assoc, ← ha, ← ha, pullback.condition_assoc]
    refine ⟨K, fun Y h i' a' hh ↦ ?_⟩
    refine eq_of_forall_comap_eq_of_mem_fpqcTopology
      (Scheme.fpqcTopology.pullback_stable h hcov) fun Z c hc ↦ ?_
    obtain ⟨j, d, hd⟩ := (Sieve.mem_ofArrows_iff ..).mp hc
    rw [← comap_comp, hd, comap_comp, hKf, ← comap_comp, ← comap_comp]
    apply hcompat
    rw [Category.assoc, ← ha, ← Category.assoc, ← hd, Category.assoc, hh, Category.assoc]
  have hex' (U : X.affineOpens) : ∃ K, Good U.1.toScheme U.1.ι K :=
    haveI : IsAffine U.1.toScheme := U.2
    hex _ _
  choose K hK using hex'
  -- gluing
  obtain ⟨J, hJ⟩ := exists_comap_ι_eq K fun U f ↦ huniq (X.affineBasicOpen f).1.ι
    (by
      have := hcomap _ (hK U) (X.homOfLE (X.basicOpen_le f))
      rw [Scheme.homOfLE_ι] at this
      exact this) (hK _)
  refine ⟨J, fun i ↦ eq_of_comap_ι_eq (p i) fun U W hW ↦ ?_⟩
  rw [← comap_comp, ← Scheme.Hom.resLE_comp_ι (p i) hW, comap_comp, hJ]
  exact hK U _ i _ (Scheme.Hom.resLE_comp_ι (p i) hW)

end Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency.types false in
/-- **Fpqc descent for finite locally free closed subschemes.** Let `f : X ⟶ T` be a morphism
of schemes, let `{g i : T i ⟶ T}` be an fpqc covering and let `p i : X i ⟶ X`,
`q i : X i ⟶ T i` exhibit `X i` as the base change `X ×_T T i`:

```
   X' i ──── p i ────▶ X
     │                 │
   q i                 f
     │                 │
     ▼                 ▼
   T' i ──── g i ────▶ T
```

Given closed subschemes `Z i ⊆ X i`, described by ideal sheaves `I i`, which are finite
locally free of degree `d` over `T i` and whose pullbacks agree over `X i ×_X X j`, there
is a unique closed subscheme `Z ⊆ X` with `Z ×_T T i = Z i`, and `Z` is finite locally
free of degree `d` over `T`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`; `det-thm-picard-descent`,
part (D2)) -/
theorem isSheaf_fpqc_finiteLocallyFreeSubscheme (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    {X : Scheme.{u}} (f : X ⟶ T) (d : ℕ)
    {X' : ι → Scheme.{u}} (p : ∀ i, X' i ⟶ X) (q : ∀ i, X' i ⟶ T' i)
    (hp : ∀ i, IsPullback (p i) (q i) f (g i)) (I : ∀ i, (X' i).IdealSheafData)
    (hfin : ∀ i, IsFinite ((I i).subschemeι ≫ q i))
    (hflat : ∀ i, Flat ((I i).subschemeι ≫ q i))
    (hfp : ∀ i, LocallyOfFinitePresentation ((I i).subschemeι ≫ q i))
    (hdeg : ∀ i (t : T' i), ((I i).subschemeι ≫ q i).finrank t = d)
    (hcompat : ∀ ⦃Y : Scheme.{u}⦄ ⦃i j : ι⦄ (a : Y ⟶ X' i) (b : Y ⟶ X' j),
      a ≫ p i = b ≫ p j → (I i).comap a = (I j).comap b) :
    ∃ J : X.IdealSheafData, (∀ i, J.comap (p i) = I i) ∧
      IsFinite (J.subschemeι ≫ f) ∧ Flat (J.subschemeι ≫ f) ∧
      LocallyOfFinitePresentation (J.subschemeι ≫ f) ∧
      (∀ t : T, (J.subschemeι ≫ f).finrank t = d) ∧
      ∀ J' : X.IdealSheafData, (∀ i, J'.comap (p i) = I i) → J' = J := by
  -- the base change `{p i : X' i ⟶ X}` of the covering is an fpqc covering of `X`
  have hpX : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X := by
    refine Scheme.fpqcTopology.superset_covering ?_ (Scheme.fpqcTopology.pullback_stable f hg)
    intro Y h hh
    obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff ..).mp hh
    exact (Sieve.mem_ofArrows_iff ..).mpr ⟨i, (hp i).lift h k hk, ((hp i).lift_fst _ _ _).symm⟩
  obtain ⟨J, hJ⟩ := Scheme.IdealSheafData.exists_comap_eq_of_mem_fpqcTopology p hpX I hcompat
  obtain rfl : I = fun i ↦ J.comap (p i) := funext fun i ↦ (hJ i).symm
  -- `Z ×_T T i` is the closed subscheme cut out by `J.comap (p i)`
  have hsq : ∀ i, IsPullback ((J.comapIso (p i)).hom ≫ pullback.snd _ _)
      ((J.comap (p i)).subschemeι ≫ q i) (J.subschemeι ≫ f) (g i) := fun i ↦
    ((IsPullback.of_hasPullback (p i) J.subschemeι).flip.paste_vert (hp i)).of_iso'
      (J.comapIso (p i)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  have : MorphismProperty.DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hfin' : IsFinite (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hfin
  have hflat' : Flat (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hflat
  have hfp' : LocallyOfFinitePresentation (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hfp
  refine ⟨J, fun _ ↦ rfl, hfin', hflat', hfp', fun t ↦ ?_, fun J' hJ' ↦
    Scheme.IdealSheafData.eq_of_comap_eq_of_mem_fpqcTopology p hpX hJ'⟩
  obtain ⟨Y, h, hh, y, rfl⟩ := Scheme.exists_mem_of_mem_fpqcTopology hg t
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff ..).mp hh
  rw [Scheme.Hom.comp_apply, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (hsq i) (k y)]
  exact hdeg i (k y)

end AlgebraicGeometry
