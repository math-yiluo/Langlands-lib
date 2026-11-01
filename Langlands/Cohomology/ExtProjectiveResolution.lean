import Langlands.Cohomology.HyperextHomComplex
import Langlands.Cohomology.SmoothHyperextSecondPage
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Ext computed with a projective resolution of the first argument

Let `C` be an abelian category with Mathlib's `Ext` groups, `X` and `Y` objects of `C` and `P` a
projective resolution of `X`. Mathlib's `P.cochainComplex` is `P` as a cochain complex indexed by
`ℤ`, with `P.complex.X k` in degree `-k`, and Mathlib identifies `Ext^n(X, Y)` with cohomology
classes of degree `n` from `P.cochainComplex` to `Y` placed in degree `0`
(`ProjectiveResolution.extAddEquivCohomologyClass`). Composing with Mathlib's
`HomComplex.homologyAddEquiv` and with `HyperextHomComplex.homComplexSingleIso`,
`extAddEquivHomology` identifies `Ext^n(X, Y)` with the cohomology in degree `n` of the complex
`Hom(P^{-•}, Y)` of `HyperextHomComplex.homObjComplex`: its term in degree `n` is the group of
morphisms `P.cochainComplex.X (-n) ⟶ Y`, and its differentials are precomposition with the
differentials of `P`, without signs. `extAddEquivHomology_extMk` evaluates this identification on
Mathlib's constructor `ProjectiveResolution.extMk`; the sign `HyperextHomComplex.sign n` appears.

For smooth representations, `smoothExtAddEquivHomology` describes the smooth Ext
`SmoothExt.ext R G V n`, the right derived functors of equivariant Hom out of `V`, in the same way
through any projective resolution of `V`. Projectivity of the first argument kills the higher Ext
groups: `isZero_ext_succ_of_projective` for smooth Ext, `isZero_secondPage_of_projective` for the
terms off the column `p = 0` on page 2 of the hyperext spectral sequence, and
`subsingleton_ext_homology_of_projective`, which says that the hypothesis on `Ext` groups in
`Langlands.Cohomology.HyperextDegenerationStatement` holds when every cohomology object of `K` is
projective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ExtProjectiveResolution

universe w w' v u

open CochainComplex HomComplex HyperextHomComplex Abelian

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X : C}
  (P : ProjectiveResolution X) (Y : C)

/-- For a projective resolution `P` of `X`, `Ext^n(X, Y)` is the cohomology in degree `n` of
the complex `Hom(P^{-•}, Y)` of `HyperextHomComplex.homObjComplex`, for the cochain complex
`P.cochainComplex` indexed by `ℤ` obtained from `P`. -/
def extAddEquivHomology (n : ℕ) :
    Ext.{w} X Y n ≃+ (homObjComplex P.cochainComplex Y).homology n :=
  P.extAddEquivCohomologyClass.trans <|
    (HomComplex.homologyAddEquiv P.cochainComplex
        ((CochainComplex.singleFunctor C 0).obj Y) n).symm.trans
      ((HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso
        (homComplexSingleIso P.cochainComplex Y)).addCommGroupIsoToAddEquiv

omit [HasExt C] in
set_option backward.isDefEq.respectTransparency false in
/-- For a cochain complex `K` indexed by `ℤ` and a cycle `c` of `Hom(K^{-•}, Y)` in degree `n`,
the cocycle of Mathlib's Hom complex from `K` to `Y` placed in degree `0` that corresponds to `c`
under `homComplexSingleIso` has underlying cochain `(cochainAddEquiv K Y n).symm` of the
underlying morphism of `c`. -/
lemma coe_cyclesIso_hom_cyclesMap (K : CochainComplex C ℤ) (n : ℤ)
    (c : (homObjComplex K Y).cycles n) :
    ((HomComplex.leftHomologyData K ((CochainComplex.singleFunctor C 0).obj Y) n).cyclesIso.hom
      (HomologicalComplex.cyclesMap (homComplexSingleIso K Y).inv n c)).1 =
      (cochainAddEquiv K Y n).symm ((homObjComplex K Y).iCycles n c) :=
  (ConcreteCategory.congr_hom (HomComplex.leftHomologyData K _ n).cyclesIso_hom_comp_i _).trans
    (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (homComplexSingleIso K Y).inv n) c)

omit [HasExt C] in
set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's `homologyAddEquiv` sends the class of a cycle `c` of Mathlib's Hom complex to the
cohomology class of the corresponding cocycle. -/
lemma homologyAddEquiv_homologyπ (K L : CochainComplex C ℤ) (n : ℤ)
    (c : (HomComplex K L).cycles n) :
    HomComplex.homologyAddEquiv K L n ((HomComplex K L).homologyπ n c) =
      CohomologyClass.mk ((HomComplex.leftHomologyData K L n).cyclesIso.hom c) :=
  ConcreteCategory.congr_hom (HomComplex.leftHomologyData K L n).homologyπ_comp_homologyIso_hom c

set_option backward.isDefEq.respectTransparency false in
/-- `extAddEquivHomology` on Mathlib's constructor `ProjectiveResolution.extMk`: let
`f : P.complex.X n ⟶ Y` vanish on the image of the differential `P.complex.d m n`, and let `c` be
a cycle of `Hom(P^{-•}, Y)` in degree `n` whose underlying morphism is `f` (transported along
`P.cochainComplexXIso`). Then `extAddEquivHomology` sends `P.extMk f m hm hf` to `sign n` times
the cohomology class of `c`. -/
lemma extAddEquivHomology_extMk {n : ℕ} (f : P.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : P.complex.d m n ≫ f = 0) (c : (homObjComplex P.cochainComplex Y).cycles n)
    (hc : ((homObjComplex P.cochainComplex Y).iCycles n c : P.cochainComplex.X (-n) ⟶ Y) =
      (P.cochainComplexXIso (-n) n rfl).hom ≫ f) :
    extAddEquivHomology P Y n (P.extMk f m hm hf) =
      sign n • (homObjComplex P.cochainComplex Y).homologyπ n c := by
  let K := homObjComplex P.cochainComplex Y
  let e := homComplexSingleIso P.cochainComplex Y
  let c' : (HomComplex P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y)).cycles n :=
    HomologicalComplex.cyclesMap e.inv n (sign n • c)
  have h₁ : (HomComplex.homologyAddEquiv P.cochainComplex _ n).symm
      (P.extAddEquivCohomologyClass (P.extMk f m hm hf)) =
      (HomComplex P.cochainComplex _).homologyπ n c' := by
    apply (HomComplex.homologyAddEquiv P.cochainComplex _ n).injective
    rw [AddEquiv.apply_symm_apply, homologyAddEquiv_homologyπ,
      ProjectiveResolution.extAddEquivCohomologyClass_apply,
      ProjectiveResolution.extEquivCohomologyClass_extMk]
    congr 1
    ext : 1
    rw [coe_cyclesIso_hom_cyclesMap, Units.smul_def, map_zsmul, hc]
    apply (cochainAddEquiv _ Y n).injective
    rw [AddEquiv.apply_symm_apply]
    change cochainAddEquiv _ Y n (Cochain.toSingleMk _ (neg_add_cancel (n : ℤ))) = _
    rw [cochainAddEquiv_toSingleMk, Units.smul_def]
  have h₂ : HomologicalComplex.homologyMap e.hom (n : ℤ)
      ((HomComplex P.cochainComplex _).homologyπ n c') =
      K.homologyπ n (HomologicalComplex.cyclesMap e.hom n c') :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e.hom (n : ℤ)) c'
  have h₃ : HomologicalComplex.cyclesMap e.hom n c' = sign n • c := by
    change (HomologicalComplex.cyclesMap e.inv n ≫ HomologicalComplex.cyclesMap e.hom n)
      (sign n • c) = _
    rw [← HomologicalComplex.cyclesMap_comp, e.inv_hom_id, HomologicalComplex.cyclesMap_id]
    rfl
  change HomologicalComplex.homologyMap e.hom (n : ℤ)
    ((HomComplex.homologyAddEquiv P.cochainComplex _ n).symm
      (P.extAddEquivCohomologyClass (P.extMk f m hm hf))) = _
  rw [h₁, h₂, h₃, Units.smul_def, map_zsmul, Units.smul_def]

end General

section Degeneration

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]

/-- If every cohomology object of `K` is projective, the Ext hypothesis of
`HyperextDegenerationStatement` holds for `K` and every `W`: `Ext^i(H^k K, W)` is zero for all
`k` and all `i > 0`. -/
theorem subsingleton_ext_homology_of_projective (K : DerivedCategory C)
    (hK : ∀ k : ℤ, Projective ((DerivedCategory.homologyFunctor C k).obj K)) (W : C) :
    ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Ext.{w'} ((DerivedCategory.homologyFunctor C k).obj K) W i) := by
  intro k i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by lia⟩
  have := hK k
  exact Ext.subsingleton_of_projective _ W n

end Degeneration

section Smooth

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- For a projective resolution `P` of a smooth representation `V`, the smooth Ext
`Ext^n(V, W)`, the `n`-th right derived functor of equivariant Hom out of `V` evaluated at `W`,
is the cohomology in degree `n` of the complex `Hom_G(P^{-•}, W)`. -/
def smoothExtAddEquivHomology {V : SmoothRep.{u, u, u} R G} (P : ProjectiveResolution V)
    (W : SmoothRep.{u, u, u} R G) (n : ℕ) :
    (SmoothExt.ext R G V n).obj W ≃+ (homObjComplex P.cochainComplex W).homology n :=
  letI := ExtRightDerived.hasExt_smoothRep R G
  (ExtRightDerived.smoothExtAddEquiv R G V W n).trans (extAddEquivHomology P W n)

/-- Smooth Ext vanishes in positive degrees when the first argument is projective. -/
theorem isZero_ext_succ_of_projective (V W : SmoothRep.{u, u, u} R G) [Projective V] (n : ℕ) :
    IsZero ((SmoothExt.ext R G V (n + 1)).obj W) := by
  have := ExtRightDerived.hasExt_smoothRep R G
  have := Ext.subsingleton_of_projective V W n
  have : Subsingleton ((SmoothExt.ext R G V (n + 1)).obj W) :=
    (ExtRightDerived.smoothExtAddEquiv R G V W (n + 1)).toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R G)]

open HyperextSpectralSequence in
/-- If `H^{-q}(K)` is projective, page 2 of the hyperext spectral sequence of `K` and `W` is
zero in positions `(p, q)` with `p > 0`. -/
theorem isZero_secondPage_of_projective (K : DerivedCategory (SmoothRep.{u, u, u} R G))
    (W : SmoothRep.{u, u, u} R G) (p q : ℤ)
    [Projective ((DerivedCategory.homologyFunctor _ (-q)).obj K)] (hp : 0 < p) :
    IsZero (((hyperextSpectralSequence DerivedCategory.TStructure.t K
      ((DerivedCategory.singleFunctor _ 0).obj W)).page 2).X ⟨p, q⟩) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = ((n + 1 : ℕ) : ℤ) := ⟨p.toNat - 1, by lia⟩
  have : Subsingleton ((SmoothExt.ext R G ((DerivedCategory.homologyFunctor _ (-q)).obj K)
      (n + 1)).obj W) :=
    ModuleCat.subsingleton_of_isZero (isZero_ext_succ_of_projective R G _ W n)
  exact AddCommGrpCat.isZero_of_iff_subsingleton.2
    (SmoothHyperext.secondPageAddEquiv R G K W (n + 1) q).toEquiv.subsingleton

end Smooth

end Langlands.Cohomology.ExtProjectiveResolution
