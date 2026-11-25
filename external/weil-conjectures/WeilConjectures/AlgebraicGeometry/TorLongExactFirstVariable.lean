/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.Algebra.Homology.FreeResolutionSesSplit
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Low-degree Tor exact sequence in the first variable

Source: Stacks Project, Algebra, Tags 00M0 and 00M3; More on Algebra, proof of
Tag 0912 (blueprint: lem-weil-pbc-tor-long-exact-first-variable).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def resolutionOfExact
    {R : Type u} [CommRing R] {Q : Type u} [AddCommGroup Q] [Module R Q]
    (F : ℕ → Type u) [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
    [∀ n, Module.Free R (F n)] (d : ∀ n, F (n + 1) →ₗ[R] F n)
    (ε : F 0 →ₗ[R] Q)
    (hε : Function.Surjective ε) (h₀ : LinearMap.ker ε = LinearMap.range (d 0))
    (hd : ∀ n, LinearMap.ker (d n) = LinearMap.range (d (n + 1))) :
    ProjectiveResolution (ModuleCat.of R Q) := by
  have sq (n : ℕ) : ModuleCat.ofHom (d (n + 1)) ≫ ModuleCat.ofHom (d n) = 0 := by
    ext x
    have hx : d (n + 1) x ∈ LinearMap.ker (d n) := by
      rw [hd n]
      exact ⟨x, rfl⟩
    exact hx
  let C := ChainComplex.of (fun n ↦ ModuleCat.of R (F n))
    (fun n ↦ ModuleCat.ofHom (d n)) sq
  have w : C.d 1 0 ≫ ModuleCat.ofHom ε = 0 := by
    dsimp [C]
    simp only [ChainComplex.of.d]
    ext x
    have hx : d 0 x ∈ LinearMap.ker ε := by
      rw [h₀]
      exact ⟨x, rfl⟩
    exact hx
  let π := (ChainComplex.toSingle₀Equiv C (ModuleCat.of R Q)).symm
    ⟨ModuleCat.ofHom ε, w⟩
  refine { complex := C, π := π, quasiIso := ?_ }
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff,
      ShortComplex.quasiIso_iff_of_zeros' _ (by simp [C,
        HomologicalComplex.shortComplexFunctor', ChainComplex.of.d])
        (by simp [HomologicalComplex.shortComplexFunctor'])
        (by simp [HomologicalComplex.shortComplexFunctor'])]
    · constructor
      · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
        simpa [π, C, HomologicalComplex.shortComplexFunctor',
          ChainComplex.of.d, ChainComplex.toSingle₀Equiv] using h₀.symm
      · change Epi (ModuleCat.ofHom ε)
        exact (ModuleCat.epi_iff_surjective _).mpr hε
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' C (n + 2) (n + 1) n (by simp) (by simp)]
      apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      simpa [C, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
        ChainComplex.of.d] using (hd n).symm
    · apply ChainComplex.exactAt_succ_single_obj

set_option backward.isDefEq.respectTransparency false in
private theorem resolutionSES
    {R : Type u} [CommRing R]
    {Q Q' Q'' : Type u} [AddCommGroup Q] [AddCommGroup Q'] [AddCommGroup Q'']
    [Module R Q] [Module R Q'] [Module R Q'']
    (u : Q →ₗ[R] Q') (v : Q' →ₗ[R] Q'')
    (hu : Function.Injective u) (hv : Function.Surjective v)
    (hExact : Function.Exact u v) :
    ∃ (P : ProjectiveResolution (ModuleCat.of R Q))
      (P' : ProjectiveResolution (ModuleCat.of R Q'))
      (P'' : ProjectiveResolution (ModuleCat.of R Q''))
      (a : P.complex ⟶ P'.complex) (b : P'.complex ⟶ P''.complex)
      (w : a ≫ b = 0),
      a.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ ModuleCat.ofHom u ∧
      b.f 0 ≫ P''.π.f 0 = P'.π.f 0 ≫ ModuleCat.ofHom v ∧
      ∀ n, Nonempty ((ShortComplex.mk a b w).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)).Splitting := by
  obtain ⟨F, F', F'', ag, mod, ag', mod', ag'', mod'', d, d', d'', ε, ε', ε'',
    α, β, π, s, hfree, hε, hε', hε'', hα, hβ, hα₀, hβ₀, hsplit⟩ :=
    Module.exists_free_resolution_ses_split R u v hu hExact hv
  let := ag
  let := mod
  let := ag'
  let := mod'
  let := ag''
  let := mod''
  let (n : ℕ) : Module.Free R (F n) := (hfree n).1
  let (n : ℕ) : Module.Free R (F' n) := (hfree n).2.1
  let (n : ℕ) : Module.Free R (F'' n) := (hfree n).2.2
  let P := resolutionOfExact F d ε hε.1 hε.2.1 hε.2.2
  let P' := resolutionOfExact F' d' ε' hε'.1 hε'.2.1 hε'.2.2
  let P'' := resolutionOfExact F'' d'' ε'' hε''.1 hε''.2.1 hε''.2.2
  let a : P.complex ⟶ P'.complex := ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (α n)) (by
      intro n
      dsimp [P, P', resolutionOfExact]
      simp only [ChainComplex.of_d]
      exact ModuleCat.hom_ext (hα n))
  let b : P'.complex ⟶ P''.complex := ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (β n)) (by
      intro n
      dsimp [P', P'', resolutionOfExact]
      simp only [ChainComplex.of_d]
      exact ModuleCat.hom_ext (hβ n))
  have w : a ≫ b = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact (hsplit n).1
  refine ⟨P, P', P'', a, b, w, ?_, ?_, ?_⟩
  · simpa [P, P', a, resolutionOfExact, ChainComplex.toSingle₀Equiv] using
      ModuleCat.hom_ext hα₀
  · simpa [P', P'', b, resolutionOfExact, ChainComplex.toSingle₀Equiv] using
      ModuleCat.hom_ext hβ₀
  · intro n
    refine ⟨{
      r := ModuleCat.ofHom (π n)
      s := ModuleCat.ofHom (s n)
      f_r := ?_
      s_g := ?_
      id := ?_ }⟩
    · apply ModuleCat.hom_ext
      exact (hsplit n).2.1
    · apply ModuleCat.hom_ext
      exact (hsplit n).2.2.1
    · apply ModuleCat.hom_ext
      exact (hsplit n).2.2.2

private noncomputable def homologyZeroIso
    {R : Type u} [CommRing R] {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [PreservesFiniteColimits F] :
    ((F.mapHomologicalComplex _).obj P.complex).homology 0 ≅ F.obj X :=
  ChainComplex.isoHomologyι₀ _ ≪≫ asIso (P.fromLeftDerivedZero' F)

set_option backward.isDefEq.respectTransparency false in
private theorem homologyZeroIso_naturality_lift
    {R : Type u} [CommRing R] {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (P' : ProjectiveResolution Y)
    (a : P.complex ⟶ P'.complex) (ha : a.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ f)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [PreservesFiniteColimits F] :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map a) 0 ≫
        (homologyZeroIso P' F).hom = (homologyZeroIso P F).hom ≫ F.map f := by
  dsimp [homologyZeroIso, ChainComplex.isoHomologyι₀]
  simp only [HomologicalComplex.isoHomologyι_hom]
  rw [HomologicalComplex.homologyι_naturality_assoc,
    ProjectiveResolution.fromLeftDerivedZero'_naturality f P P' a ha F]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem homologyZeroIso_naturality_functor
    {R : Type u} [CommRing R] {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    {F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R} [F.Additive] [G.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] (α : F ⟶ G) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α _).app P.complex) 0 ≫
        (homologyZeroIso P G).hom = (homologyZeroIso P F).hom ≫ α.app X := by
  dsimp [homologyZeroIso, ChainComplex.isoHomologyι₀]
  simp only [HomologicalComplex.isoHomologyι_hom]
  rw [HomologicalComplex.homologyι_naturality_assoc]
  simp only [Category.assoc]
  apply congrArg (fun k ↦ _ ≫ k)
  rw [← cancel_epi (HomologicalComplex.pOpcycles
    ((F.mapHomologicalComplex _).obj P.complex) 0)]
  simp only [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
  exact (α.naturality (P.π.f 0)).symm

private theorem exact_of_iso
    {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{u} R)} (hS : S.Exact)
    {X₁ X₂ X₃ : ModuleCat.{u} R} (e₁ : S.X₁ ≅ X₁) (e₂ : S.X₂ ≅ X₂)
    (e₃ : S.X₃ ≅ X₃) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hf : S.f ≫ e₂.hom = e₁.hom ≫ f) (hg : S.g ≫ e₃.hom = e₂.hom ≫ g) :
    Function.Exact f.hom g.hom := by
  have w : f ≫ g = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, ← hf, Category.assoc, ← hg,
      ← Category.assoc, S.zero, zero_comp, comp_zero]
  let T := ShortComplex.mk f g w
  have he : T.Exact := ShortComplex.exact_of_iso
    (ShortComplex.isoMk e₁ e₂ e₃ hf.symm hg.symm) hS
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp he

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The low-degree Tor sequence for a short exact sequence in the first variable,
with an `R`-linear connecting map natural in the second variable.

Source: Stacks Project, Algebra, Tags 00M0 and 00M3; More on Algebra, proof of
Tag 0912. The direct proof below uses Algebra 065P and Homology 0111.
(blueprint: lem-weil-pbc-tor-long-exact-first-variable)

1. By `theorem-finite-etale-covers-proper-henselian--2`, choose free resolutions `F`, `F'`,
   `F''` of `Q`, `Q'`, `Q''`, with augmentation-compatible lifts `α` of `u` and `β`
   of `v`. Choose degreewise splittings `π`, `s` with `βα = 0`, `πα = 1`, `βs = 1`,
   and `απ + sβ = 1`. Fix these choices independently of `N`.
2. Tensor the resolutions and their maps with `N`. The splitting identities persist,
   so the resulting complexes `C`, `C'`, `C''` form a degreewise short exact sequence.
   For every `g : N →ₗ[R] N'`, the chain maps `1 ⊗ g` commute with `α ⊗ 1`,
   `β ⊗ 1`, and the differentials, by the tensor product map composition identities.
3. By `def-weil-pbc-tor-modules`, identify Tor in degree one with the homology of
   these complexes. By `lem-weil-pbc-tor-map-via-resolution-lift`, the maps induced
   by `β ⊗ 1` and `1 ⊗ g` are respectively `Tor₁(v,N)` and `Tor₁(Q'',g)`.
   By `lem-weil-pbc-tensor-right-exact`, the augmentations induce isomorphisms
   `c_N : H₀(C) ≅ Q ⊗ N` and similarly for `C'`; these commute with `u ⊗ 1`
   and `1 ⊗ g` because the augmentations do.
4. Apply `lem-weil-pbc-snake-lemma-modules` to the diagram with top row
   `C₁ / im d₂ → C'₁ / im d'₂ → C''₁ / im d''₂ → 0` and bottom row
   `0 → C₀ → C'₀ → C''₀`. The bottom is exact by step 2. For top exactness,
   if `β y = d'' z''`, lift `z''` along the surjective `β₂` to `z'`; then
   `y - d' z'` lies in `ker β₁ = im α₁`. The top last map is surjective as `β₁`
   is. The vertical kernels and cokernels are `H₁` and `H₀`. The snake map
   `∂_N : H₁(C'') → H₀(C)` sends a cycle class `[z]` to `[w]`, where
   `β₁ y = z` and `α₀ w = d'₁ y`; its value is independent of the choices.
5. Compose the Tor-to-homology isomorphism, `∂_N`, and `c_N` to obtain `δ_N`.
   Transport snake exactness to exactness at `Tor₁(Q'',N)` and `Q ⊗ N` using
   step 3. Exactness at `Q' ⊗ N` and surjectivity of `v ⊗ 1` follow from
   `lem-weil-pbc-tensor-right-exact` applied to the original short exact sequence.
6. Given `g`, the images of the choices `y,w` under `1 ⊗ g` are admissible choices
   for the image of `z`, by step 2. The snake formula therefore gives
   `∂_{N'} H₁(1 ⊗ g) = H₀(1 ⊗ g) ∂_N`. Transport through the natural
   identifications of step 3 to obtain `(1 ⊗ g) δ_N = δ_{N'} Tor₁(Q'',g)`.
   The other squares commute by tensor bifunctoriality and, for the Tor map,
   `lem-weil-pbc-tor-map-via-resolution-lift` applied to `β ⊗ g`.
-/
theorem tor_long_exact_first_variable
    {R : Type u} [CommRing R]
    {Q Q' Q'' : Type u} [AddCommGroup Q] [AddCommGroup Q'] [AddCommGroup Q'']
    [Module R Q] [Module R Q'] [Module R Q'']
    (u : Q →ₗ[R] Q') (v : Q' →ₗ[R] Q'')
    (hu : Function.Injective u) (hv : Function.Surjective v)
    (hExact : Function.Exact u v) :
    ∃ δ : (∀ (N : Type u) [AddCommGroup N] [Module R N],
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R Q'')).obj
            (ModuleCat.of R N)) ⟶ ModuleCat.of R (Q ⊗[R] N)),
      (∀ (N : Type u) [AddCommGroup N] [Module R N],
        Function.Exact
          (((Tor' (ModuleCat R) 1).map (ModuleCat.ofHom v)).app
            (ModuleCat.of R N)).hom (δ N).hom ∧
        Function.Exact (δ N).hom (u.rTensor N) ∧
        Function.Exact (u.rTensor N) (v.rTensor N) ∧
        Function.Surjective (v.rTensor N)) ∧
      (∀ (N N' : Type u) [AddCommGroup N] [Module R N]
        [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N'),
        (MonoidalCategory.tensorHom (𝟙 (ModuleCat.of R Q))
          (ModuleCat.ofHom g)).hom.comp (δ N).hom =
          (δ N').hom.comp
            (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R Q'')).map
              (ModuleCat.ofHom g)).hom) := by
  classical
  obtain ⟨P, P', P'', a, b, w, ha, hb, hs⟩ := resolutionSES u v hu hv hExact
  let S := ShortComplex.mk a b w
  let F (N : ModuleCat.{u} R) := (MonoidalCategory.tensoringRight (ModuleCat R)).obj N
  let SN (N : ModuleCat.{u} R) := S.map ((F N).mapHomologicalComplex (ComplexShape.down ℕ))
  have hSN (N : ModuleCat.{u} R) : (SN N).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact ((hs n).some.map (F N)).shortExact
  let δ (N : ModuleCat.{u} R) :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R Q'')).obj N) ⟶
        (F N).obj (ModuleCat.of R Q) :=
    (P''.isoLeftDerivedObj (F N) 1).hom ≫
      (hSN N).δ 1 0 (by simp) ≫ (homologyZeroIso P (F N)).hom
  refine ⟨fun N _ _ ↦ δ (ModuleCat.of R N), ?_, ?_⟩
  · intro N _ _
    let M := ModuleCat.of R N
    refine ⟨?_, ?_, rTensor_exact N hExact hv, v.rTensor_surjective N hv⟩
    · apply exact_of_iso ((hSN M).homology_exact₃ 1 0 (by simp))
        (P'.isoLeftDerivedObj (F M) 1).symm
        (P''.isoLeftDerivedObj (F M) 1).symm (homologyZeroIso P (F M))
      · exact (P'.isoLeftDerivedObj_inv_naturality
          (ModuleCat.ofHom v) P'' b hb (F M) 1).symm
      · simp only [δ, M, Iso.symm_hom, Iso.inv_hom_id_assoc]
    · apply exact_of_iso ((hSN M).homology_exact₁ 1 0 (by simp))
        (P''.isoLeftDerivedObj (F M) 1).symm (homologyZeroIso P (F M))
        (homologyZeroIso P' (F M))
      · simp only [δ, M, Iso.symm_hom, Iso.inv_hom_id_assoc]
      · exact homologyZeroIso_naturality_lift (ModuleCat.ofHom u) P P' a ha (F M)
  · intro N N' _ _ _ _ g
    let M := ModuleCat.of R N
    let M' := ModuleCat.of R N'
    let α : F M ⟶ F M' :=
      (MonoidalCategory.tensoringRight (ModuleCat R)).map (ModuleCat.ofHom g)
    let φ : SN M ⟶ SN M' := {
      τ₁ := (NatTrans.mapHomologicalComplex α _).app P.complex
      τ₂ := (NatTrans.mapHomologicalComplex α _).app P'.complex
      τ₃ := (NatTrans.mapHomologicalComplex α _).app P''.complex
      comm₁₂ := ((NatTrans.mapHomologicalComplex α _).naturality a).symm
      comm₂₃ := ((NatTrans.mapHomologicalComplex α _).naturality b).symm }
    have h₀ := homologyZeroIso_naturality_functor P α
    have h₁ := P''.leftDerived_app_eq α 1
    have hboundary := HomologicalComplex.HomologySequence.δ_naturality φ (hSN M) (hSN M')
      1 0 (by simp)
    have hδ : δ M ≫ α.app (ModuleCat.of R Q) =
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R Q'')).map
          (ModuleCat.ofHom g)) ≫ δ M' := by
      simp only [δ, Category.assoc]
      rw [← h₀]
      rw [← Category.assoc ((hSN M).δ 1 0 (by simp)), hboundary]
      change _ = (NatTrans.leftDerived α 1).app (ModuleCat.of R Q'') ≫ _
      rw [h₁]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    exact congrArg ModuleCat.Hom.hom hδ

end CategoryTheory
