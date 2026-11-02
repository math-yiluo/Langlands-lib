import Mathlib
import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection

/-!
# Trivializing a line bundle by a combination of global sections

Let `f : X ⟶ Spec B` be universally closed and let `N` be an invertible module on `X` with
finitely many global sections `m i`. Suppose that at a field point `B → K` the pullback of `N`
to the fibre `X_K` is trivial, and that every global section of `N_K` is a `K`-linear
combination of the pullbacks of the `m i`. Then there is a flat finitely presented `B`-algebra
`A`, with a prime over the kernel of `B → K`, such that `N` becomes trivial on every scheme
mapping compatibly to `X` and `Spec A`.

The proof is the polynomial trick. Over `C = B[T_i]` the generic combination `∑ T_i • m i`
pulls back, at the `C`-point `T ↦ c` of `K`, to a trivializing frame of `N_K`. A frame-lifting
theorem from the FLT port gives `g ∈ C`, nonzero at that point, such that the generic
combination frames `N_C` near every point over `D(g)`. Take `A = C[1/g]`.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.FrameCombination

open Scheme.Modules

section Frames

variable {X : Scheme.{u}}

/-- A global section that frames a module near every point trivializes the module. -/
theorem nonempty_iso_unit_of_forall_isFrameOn (M : X.Modules) (s : Γ(M, ⊤))
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsFrameOn s U) :
    Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf) := by
  choose U hxU hU using h
  have : IsIso (Langlands.SchemeModule.sectionHom M s) :=
    isIso_of_isFrameOn_of_iSup_eq_top (Langlands.SchemeModule.sectionHom M s) U
      (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩)
      (fun x => unitSection (U x)) (fun x => M.presheaf.map (homOfLE le_top).op s)
      (fun x => isFrameOn_unitSection _) (fun x => (hU x).map (homOfLE le_top))
      (fun x => Langlands.SchemeModule.sectionHom_app_one M s (U x))
  exact ⟨(asIso (Langlands.SchemeModule.sectionHom M s)).symm⟩

/-- A trivial module has a global frame. -/
theorem exists_isFrameOn_top_of_iso_unit {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) : ∃ τ : Γ(M, ⊤), IsFrameOn τ ⊤ :=
  ⟨e.inv.app ⊤ (unitSection ⊤), (isFrameOn_unitSection (U := ⊤) ⊤).map_iso e.symm⟩

end Frames

section Combination

variable {Z Y X : Scheme.{u}}

/-- The pullback of a global section, as a global section of the pullback module. -/
def pullbackGlobalSection (φ : Y ⟶ X) {N : X.Modules} (s : Γ(N, ⊤)) :
    Γ((Scheme.Modules.pullback φ).obj N, ⊤) :=
  pullbackLocalSection φ s

lemma pullbackGlobalSection_def (φ : Y ⟶ X) {N : X.Modules} (s : Γ(N, ⊤)) :
    pullbackGlobalSection φ s = pullbackLocalSection φ s := rfl

lemma pullbackGlobalSection_sum (φ : Y ⟶ X) {N : X.Modules} {κ : Type*} (S : Finset κ)
    (s : κ → Γ(N, ⊤)) :
    pullbackGlobalSection φ (∑ i ∈ S, s i) = ∑ i ∈ S, pullbackGlobalSection φ (s i) :=
  pullbackLocalSection_sum φ S s

lemma pullbackGlobalSection_smul (φ : Y ⟶ X) {N : X.Modules} (g : Γ(X, ⊤)) (s : Γ(N, ⊤)) :
    pullbackGlobalSection φ (g • s) = φ.appTop g • pullbackGlobalSection φ s :=
  pullbackLocalSection_smul φ g s

lemma pullbackComp_app_pullbackGlobalSection (φ : Z ⟶ Y) (a : Y ⟶ X) (N : X.Modules)
    (s : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackComp φ a).hom.app N).app ⊤
        (pullbackGlobalSection φ (pullbackGlobalSection a s)) =
      pullbackGlobalSection (φ ≫ a) s :=
  P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection.PicTanH.pullbackComp_hom_app_app_pullbackLocalSection
    φ a N ⊤ s

variable {ι : Type*} [Fintype ι]

/-- The combination `∑ i, k i • φ^* (m i)` of pulled back global sections. -/
def comb (φ : Y ⟶ X) (N : X.Modules) (m : ι → Γ(N, ⊤)) (k : ι → Γ(Y, ⊤)) :
    Γ((Scheme.Modules.pullback φ).obj N, ⊤) :=
  ∑ i, k i • pullbackGlobalSection φ (m i)

lemma pullbackComp_app_comb (φ : Z ⟶ Y) (a : Y ⟶ X) (N : X.Modules) (m : ι → Γ(N, ⊤))
    (k : ι → Γ(Y, ⊤)) :
    ((Scheme.Modules.pullbackComp φ a).hom.app N).app ⊤ (pullbackGlobalSection φ (comb a N m k)) =
      comb (φ ≫ a) N m (fun i => φ.appTop (k i)) := by
  rw [comb, comb, pullbackGlobalSection_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pullbackGlobalSection_smul, Scheme.Modules.Hom.app_smul]
  exact congrArg _ (pullbackComp_app_pullbackGlobalSection φ a N (m i))

lemma isFrameOn_pullbackGlobalSection_comb_iff (φ : Z ⟶ Y) (a : Y ⟶ X) (N : X.Modules)
    (m : ι → Γ(N, ⊤)) (k : ι → Γ(Y, ⊤)) (V : Z.Opens) :
    IsFrameOn (pullbackGlobalSection φ (comb a N m k)) V ↔
      IsFrameOn (comb (φ ≫ a) N m (fun i => φ.appTop (k i))) V := by
  rw [← pullbackComp_app_comb]
  exact ⟨fun h => h.map_iso ((Scheme.Modules.pullbackComp φ a).app N),
    P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection.PicTanH.isFrameOn_of_map_iso
      ((Scheme.Modules.pullbackComp φ a).app N)⟩

end Combination

section Main

open Scheme.TwoAffineOpenCover (specMap)

lemma specMap_comp (B C K : Type u) [CommRing B] [CommRing C] [CommRing K] [Algebra B C]
    [Algebra C K] [Algebra B K] [IsScalarTower B C K] :
    specMap C K ≫ specMap B C = specMap B K := by
  rw [specMap, specMap, specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

variable {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [UniversallyClosed f]

/-- **Polynomial trick.** If an invertible module `N` on `X` becomes trivial on the fibre over a
field point `B → K`, and the sections of the fibre are spanned over `K` by pullbacks of finitely
many global sections `m i`, then `N` becomes trivial after a flat finitely presented base change
`B → A` whose image contains the point, on every scheme mapping compatibly to `X` and
`Spec A`. -/
theorem exists_flat_trivialization_of_span (N : X.Modules) (hN : IsInvertible N)
    {ι : Type} [Fintype ι] (m : ι → Γ(N, ⊤)) (K : Type u) [Field K] [Algebra B K]
    (htriv : Nonempty ((Scheme.Modules.pullback (pullback.fst f (specMap B K))).obj N ≅
      SheafOfModules.unit (pullback f (specMap B K)).ringCatSheaf))
    (hspan : ∀ s : Γ((Scheme.Modules.pullback (pullback.fst f (specMap B K))).obj N, ⊤),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd f (specMap B K))
        ((Scheme.Modules.pullback (pullback.fst f (specMap B K))).obj N) ⊤
      ∃ c : ι → K, s = ∑ i, c i • pullbackGlobalSection (pullback.fst f (specMap B K)) (m i)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra B A), Module.Flat B A ∧
      Algebra.FinitePresentation B A ∧
      (∃ q : PrimeSpectrum A, q.asIdeal.comap (algebraMap B A) = RingHom.ker (algebraMap B K)) ∧
      ∀ {Z : Scheme.{u}} (a : Z ⟶ X) (b : Z ⟶ Spec (.of A)), a ≫ f = b ≫ specMap B A →
        Nonempty ((Scheme.Modules.pullback a).obj N ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  classical
  -- A frame of the fibre and its coefficients.
  obtain ⟨e⟩ := htriv
  obtain ⟨τ, hτ⟩ := exists_isFrameOn_top_of_iso_unit e
  obtain ⟨c, hc⟩ := hspan τ
  -- The polynomial ring and the point `T ↦ c`.
  let C := MvPolynomial ι B
  let φ : C →ₐ[B] K := MvPolynomial.aeval c
  let : Algebra C K := φ.toRingHom.toAlgebra
  have : IsScalarTower B C K := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hφ : ∀ i, algebraMap C K (MvPolynomial.X i) = c i := fun i => MvPolynomial.aeval_X c i
  -- The base change to `C` and the generic combination.
  let pC := pullback.fst f (specMap B C)
  let fC := pullback.snd f (specMap B C)
  let NC := (Scheme.Modules.pullback pC).obj N
  have hNC : IsInvertible NC := IsInvertible.pullback pC hN
  let xC : ι → Γ(pullback f (specMap B C), ⊤) := fun i =>
    fC.appTop ((Scheme.ΓSpecIso (.of C)).inv (MvPolynomial.X i))
  let σ : Γ(NC, ⊤) := comb pC N m xC
  -- The fibre of `X_C` over the point, and its map to the fibre of `X` over `K`.
  let qK := pullback.fst fC (specMap C K)
  let sK := pullback.snd fC (specMap C K)
  let π := pullback.fst f (specMap B K)
  let κ := pullback.snd f (specMap B K)
  let ψ : pullback fC (specMap C K) ⟶ pullback f (specMap B K) :=
    pullback.lift (qK ≫ pC) sK (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, specMap_comp])
  have hψπ : ψ ≫ π = qK ≫ pC := pullback.lift_fst _ _ _
  have hψκ : ψ ≫ κ = sK := pullback.lift_snd _ _ _
  -- The coefficients of `τ` as global functions on the fibre.
  let kK : ι → Γ(pullback f (specMap B K), ⊤) := fun i =>
    κ.appTop ((Scheme.ΓSpecIso (.of K)).inv (c i))
  have hκ : κ.appLE ⊤ ⊤ le_top = κ.appTop := (Scheme.Hom.app_eq_appLE κ).symm
  have hc' : τ = comb π N m kK := by
    rw [hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ((Scheme.ΓSpecIso (.of K)).inv ≫ κ.appLE ⊤ ⊤ le_top) (c i) •
        pullbackGlobalSection π (m i) = kK i • pullbackGlobalSection π (m i)
    rw [hκ]
    rfl
  have hscal : (fun i => ψ.appTop (kK i)) = fun i => qK.appTop (xC i) := by
    funext i
    have hnat : ∀ y, (specMap C K).appTop ((Scheme.ΓSpecIso (.of C)).inv y) =
        (Scheme.ΓSpecIso (.of K)).inv (algebraMap C K y) := by
      intro y
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    change (κ.appTop ≫ ψ.appTop) _ = (fC.appTop ≫ qK.appTop) _
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hψκ, pullback.condition,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hnat, hφ]
  -- The generic combination frames the fibre of `N_C` over the point.
  have hframe : IsFrameOn (pullbackGlobalSection qK σ) ⊤ := by
    have h1 : IsFrameOn (pullbackGlobalSection ψ (comb π N m kK)) ⊤ := by
      rw [← hc']
      exact hτ.pullbackLocalSection ψ
    rw [isFrameOn_pullbackGlobalSection_comb_iff, hψπ, hscal] at h1
    exact (isFrameOn_pullbackGlobalSection_comb_iff qK pC N m xC ⊤).2 h1
  -- Frame lifting from the FLT port.
  obtain ⟨g, hg, hloc⟩ := exists_basicOpen_forall_exists_frame_of_frame_pullback fC NC hNC
    (fun _ : Unit => σ) K ⟨RingHom.ker (algebraMap C K), RingHom.ker_isPrime _⟩ rfl
    (fun z => ⟨(), ⊤, trivial, fun V' _ => hframe le_top le_top⟩)
  -- The localization `A = C[1/g]`.
  let A := Localization.Away g
  have hsA : specMap C A ≫ specMap B C = specMap B A := specMap_comp B C A
  refine ⟨A, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · have : Module.Flat C A := IsLocalization.flat A (Submonoid.powers g)
    exact Module.Flat.trans B C A
  · have : Algebra.FinitePresentation C A := IsLocalization.Away.finitePresentation g
    exact Algebra.FinitePresentation.trans B C A
  · obtain ⟨q, hq⟩ : (⟨RingHom.ker (algebraMap C K), RingHom.ker_isPrime _⟩ : PrimeSpectrum C) ∈
        Set.range (PrimeSpectrum.comap (algebraMap C A)) := by
      rw [PrimeSpectrum.localization_away_comap_range A g]
      exact hg
    refine ⟨q, ?_⟩
    rw [IsScalarTower.algebraMap_eq B C A, ← Ideal.comap_comap]
    have hq' := congrArg PrimeSpectrum.asIdeal hq
    rw [PrimeSpectrum.comap_asIdeal] at hq'
    rw [hq', RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]
  · intro Z a b hab
    let θ : Z ⟶ pullback f (specMap B C) :=
      pullback.lift a (b ≫ specMap C A) (by rw [hab, Category.assoc, hsA])
    have hθ : θ ≫ pC = a := pullback.lift_fst _ _ _
    have hθC : θ ≫ fC = b ≫ specMap C A := pullback.lift_snd _ _ _
    suffices hZ : Nonempty ((Scheme.Modules.pullback θ).obj NC ≅
        SheafOfModules.unit Z.ringCatSheaf) by
      obtain ⟨eZ⟩ := hZ
      exact ⟨(Scheme.Modules.pullbackCongr hθ.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp θ pC).app N).symm ≪≫ eZ⟩
    refine nonempty_iso_unit_of_forall_isFrameOn _ (pullbackGlobalSection θ σ) fun z => ?_
    have hz : fC (θ z) ∈ PrimeSpectrum.basicOpen g := by
      have : fC (θ z) = specMap C A (b z) := by
        rw [← Scheme.Hom.comp_apply, hθC, Scheme.Hom.comp_apply]
      rw [this, specMap, Spec.map_apply]
      intro hmem
      exact (b z).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.Away.algebraMap_isUnit g))
    obtain ⟨_, U, hU, hUfr⟩ := hloc (θ z) hz
    exact ⟨θ ⁻¹ᵁ U, hU, (show IsFrameOn σ U from fun W _ hWV => hUfr W hWV).pullbackLocalSection θ⟩

end Main

end Langlands.AlgebraicGeometry.Picard.FrameCombination
