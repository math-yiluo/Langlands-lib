import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingProof
import Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Support
import Langlands.AlgebraicGeometry.Modules.NoetherianVanishing.Topology

/-!
# Vanishing of cohomology by induction on the dimension of the support

Let `X` be a noetherian separated scheme over `Spec R`. If an `𝒪_X`-module `M` is quasi-coherent
on every affine open and vanishes off a closed set `Z` all of whose irreducible closed subsets
have height `< e`, then `Hⁿ(X, M) = 0` for `n ≥ e`.

The proof is an induction on `e`, and for fixed `e` a noetherian induction on `Z`. Choose an
irreducible closed `T ⊆ Z`, a point `η ∈ T` and an affine open `V ∋ η` with `V ∩ Z ⊆ T`, and
let `j : Spec Γ(X, V) ⟶ X` be the open immersion onto `V`. The unit `M ⟶ j_* (M|_V)` factors
as an epimorphism onto its image `I` followed by a monomorphism. The kernel vanishes off
`Z \ V`, a proper closed subset of `Z`. The cokernel vanishes off `T \ V`, whose irreducible
closed subsets have height `< e - 1`. The cohomology of `j_* (M|_V)` vanishes in positive
degrees because `j` is affine. The two long exact sequences give the result.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order

namespace Langlands.AlgebraicGeometry.Modules

namespace NoetherianVanishing

open QuasicoherentLocal

variable {X : Scheme.{u}}

lemma isAffineHom_fromSpec [X.IsSeparated] {V : X.Opens} (hV : IsAffineOpen V) :
    IsAffineHom hV.fromSpec := by
  have : IsAffineHom (hV.fromSpec ≫ terminal.from X) := isAffineHom_of_isAffine _
  exact IsAffineHom.of_comp hV.fromSpec (terminal.from X)

/-- On a separated scheme, the pushforward of a quasi-coherent module along the inclusion of
an affine open has vanishing positive-degree cohomology. -/
theorem isZero_relativeCohomology_pushforward_fromSpec [X.IsSeparated] {V : X.Opens}
    (hV : IsAffineOpen V) {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (G : (Spec Γ(X, V)).Modules) [G.IsQuasicoherent] (q : ℕ) :
    IsZero ((DerivedSections.relativeCohomology f (q + 1)).obj
      ((Scheme.Modules.pushforward hV.fromSpec).obj G)) := by
  have := isAffineHom_fromSpec hV
  have hG : ∀ q : ℕ, IsZero ((DerivedSections.higherDirectImage hV.fromSpec (q + 1)).obj G) :=
    fun q => AffineVanishing.isZero_higherDirectImage_of_isCechAcyclic hV.fromSpec q G
      (AffineVanishing.isCechAcyclic_of_isQuasicoherent G)
  have hJ : ∀ J : (Spec Γ(X, V)).Modules, Injective J → ∀ q : ℕ,
      IsZero ((DerivedSections.relativeCohomology f (q + 1)).obj
        ((Scheme.Modules.pushforward hV.fromSpec).obj J)) :=
    fun J hJ q => (pushforwardInjectiveAcyclic _ _ hV.fromSpec J hJ q).2 R f
  have := DerivedSections.isIso_pushforwardComparison hV.fromSpec f G hG hJ (q + 1)
  exact ((affineQuasicoherentCohomologyVanishing (Spec Γ(X, V)) inferInstance G inferInstance
    q).2 R (hV.fromSpec ≫ f)).of_iso (asIso (DerivedSections.pushforwardComparison hV.fromSpec f G hG (q + 1))).symm

lemma VanishesOn.bot (M : X.Modules) : VanishesOn M ⊥ := by
  intro W hW s
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (F := F) (U := (PEmpty.elim : PEmpty.{u + 1} → X.Opens))
    W (fun i => i.elim) (by rw [iSup_of_empty]; exact hW) s 0 (fun i => i.elim)

lemma isZero_of_vanishesOn_top {M : X.Modules} (h : VanishesOn M ⊤) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  exact (h W le_top _).trans (h W le_top _).symm

lemma isZero_relativeCohomology_of_isZero {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    {M : X.Modules} (hM : IsZero M) (n : ℕ) :
    IsZero ((DerivedSections.relativeCohomology f n).obj M) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, hM.eq_of_src (𝟙 M) 0]
  exact Langlands.Cohomology.DerivedPlus.rightDerived_map_zero
    (DerivedSections.relativeGlobalSections f) n M M

variable [IsNoetherian X] [X.IsSeparated] {R : CommRingCat.{u}} (f : X ⟶ Spec R)

/-- Vanishing of cohomology above the height bound of a closed set off which `M` vanishes. -/
theorem isZero_relativeCohomology_of_height (e : ℕ) :
    ∀ (Z : Closeds X) (M : X.Modules), IsAffineLocallyQuasicoherent M →
      VanishesOn M Z.compl → (∀ T : IrreducibleCloseds X, (T : Set X) ⊆ Z → height T < e) →
      ∀ n, e ≤ n → IsZero ((DerivedSections.relativeCohomology f n).obj M) := by
  induction e with
  | zero =>
    intro Z M _ hMZ hZ n _
    have hZe : (Z : Set X) = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
      have := hZ ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
        (closure_minimal (Set.singleton_subset_iff.2 hx) Z.isClosed)
      simp at this
    have hM0 : IsZero M := isZero_of_vanishesOn_top (hMZ.mono (fun x _ => by
      change x ∈ (Z : Set X)ᶜ
      rw [hZe]
      exact Set.notMem_empty x))
    exact isZero_relativeCohomology_of_isZero f hM0 n
  | succ e ih =>
    intro Z
    induction Z using WellFoundedLT.induction with
    | _ Z IH =>
    intro M hM hMZ hZ n hn
    by_cases hZe : (Z : Set X) = ∅
    · have hM0 : IsZero M := isZero_of_vanishesOn_top (hMZ.mono (fun x _ => by
        change x ∈ (Z : Set X)ᶜ
        rw [hZe]
        exact Set.notMem_empty x))
      exact isZero_relativeCohomology_of_isZero f hM0 n
    obtain ⟨T, O₀, hTZ, ⟨η, hηO, hηZ⟩, hOT⟩ :=
      exists_irreducibleCloseds_inter_subset Z (Set.nonempty_iff_ne_empty.2 hZe)
    obtain ⟨V, hV, hηV, hVO⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hηO
    have hV' : IsAffineOpen V := hV
    have := isAffineHom_fromSpec hV'
    have hjr : hV'.fromSpec.opensRange = V := hV'.opensRange_fromSpec
    have hGqc : (M.restrict hV'.fromSpec).IsQuasicoherent := hM V hV'
    let J := (Scheme.Modules.pushforward hV'.fromSpec).obj (M.restrict hV'.fromSpec)
    let φ : M ⟶ J := unitMap hV'.fromSpec M
    let p := Abelian.factorThruImage φ
    let i := Abelian.image.ι φ
    have hJ : IsAffineLocallyQuasicoherent J :=
      IsAffineLocallyQuasicoherent.pushforward hV'.fromSpec
        (IsAffineLocallyQuasicoherent.of_isQuasicoherent _)
    have eK : kernel φ ≅ kernel p :=
      (kernelIsoOfEq (Abelian.image.fac φ)).symm ≪≫ kernelCompMono p i
    have eC : cokernel φ ≅ cokernel i :=
      (cokernelIsoOfEq (Abelian.image.fac φ)).symm ≪≫ cokernelEpiComp p i
    have hK : IsAffineLocallyQuasicoherent (kernel p) :=
      (IsAffineLocallyQuasicoherent.kernel φ hM hJ).of_iso eK
    have hC : IsAffineLocallyQuasicoherent (cokernel i) :=
      (IsAffineLocallyQuasicoherent.cokernel φ hM hJ).of_iso eC
    -- the kernel vanishes off `Z \ V`
    let Z' : Closeds X := ⟨(Z : Set X) ∩ (V : Set X)ᶜ, Z.isClosed.inter V.isOpen.isClosed_compl⟩
    have hZ'Z : Z' < Z := by
      refine lt_of_le_of_ne (fun x hx => hx.1) (fun h => ?_)
      have : η ∈ (Z' : Set X) := by rw [h]; exact hηZ
      exact this.2 hηV
    have hKsupp : VanishesOn (kernel p) Z'.compl := by
      have h1 : VanishesOn (kernel φ) (Z.compl ⊔ V) :=
        (hMZ.kernel φ).sup (hjr ▸ vanishesOn_kernel_unitMap hV'.fromSpec M)
      refine (h1.mono ?_).of_iso eK
      intro x hx
      by_cases hxV : x ∈ V
      · exact Or.inr hxV
      · exact Or.inl (fun hxZ => hx ⟨hxZ, hxV⟩)
    have hZ'h : ∀ T' : IrreducibleCloseds X, (T' : Set X) ⊆ Z' → height T' < (e + 1 : ℕ) :=
      fun T' h => hZ T' (h.trans (fun x hx => hx.1))
    -- the cokernel vanishes off `T \ V`
    let T' : Closeds X := ⟨(T : Set X) ∩ (V : Set X)ᶜ, T.isClosed.inter V.isOpen.isClosed_compl⟩
    let Tc : X.Opens := ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩
    have hJT : VanishesOn J Tc := by
      refine vanishesOn_pushforward_restrict hV'.fromSpec M hMZ (fun W hW => ?_)
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hjr]
      rintro x ⟨hxV, hxW⟩ hxZ
      exact hW hxW (hOT ⟨hVO hxV, hxZ⟩)
    have hCsupp : VanishesOn (cokernel i) T'.compl := by
      have h1 : VanishesOn (cokernel φ) (Tc ⊔ V) :=
        (VanishesOn.cokernel_of_right φ hJT).sup
          (hjr ▸ vanishesOn_cokernel_unitMap hV'.fromSpec M)
      refine (h1.mono ?_).of_iso eC
      intro x hx
      by_cases hxV : x ∈ V
      · exact Or.inr hxV
      · exact Or.inl (fun hxT => hx ⟨hxT, hxV⟩)
    have hT'h : ∀ T'' : IrreducibleCloseds X, (T'' : Set X) ⊆ T' → height T'' < e := by
      intro T'' hT''
      have h1 : height T'' + 1 ≤ height T :=
        height_add_one_le_of_subset (fun x hx => (hT'' hx).1) (hOT ⟨hηO, hηZ⟩)
          (fun h => (hT'' h).2 hηV)
      have h2 : height T ≤ e := by
        have h3 := hZ T hTZ
        push_cast at h3
        exact (ENat.lt_add_one_iff (ENat.natCast_ne_top e)).1 h3
      exact (ENat.add_one_le_iff' (ENat.natCast_ne_top e)).1 (h1.trans h2)
    -- cohomology
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hKn : IsZero ((DerivedSections.relativeCohomology f (m + 1)).obj (kernel p)) :=
      IH Z' hZ'Z (kernel p) hK hKsupp hZ'h (m + 1) hn
    have hCm : IsZero ((DerivedSections.relativeCohomology f m).obj (cokernel i)) :=
      ih T' (cokernel i) hC hCsupp hT'h m (by omega)
    have hJn : IsZero ((DerivedSections.relativeCohomology f (m + 1)).obj J) :=
      isZero_relativeCohomology_pushforward_fromSpec hV' f _ m
    let := HasDerivedCategory.standard X.Modules
    let := HasDerivedCategory.standard (ModuleCat.{u} R)
    let F := DerivedSections.relativeGlobalSections f
    have hS₁ : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
    have hS₂ : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
    have hI : IsZero ((F.rightDerived (m + 1)).obj (Abelian.image φ)) := by
      have hE := Langlands.Cohomology.DerivedPlus.rightDerived_exact₁ F hS₂ m (m + 1) rfl
      exact hE.isZero_X₂_iff.2 ⟨hCm.eq_of_src _ _, hJn.eq_of_tgt _ _⟩
    have hE := Langlands.Cohomology.DerivedPlus.rightDerived_exact₂ F hS₁ (m + 1)
    exact hE.isZero_X₂_iff.2 ⟨hKn.eq_of_src _ _, hI.eq_of_tgt _ _⟩

end NoetherianVanishing

end Langlands.AlgebraicGeometry.Modules
