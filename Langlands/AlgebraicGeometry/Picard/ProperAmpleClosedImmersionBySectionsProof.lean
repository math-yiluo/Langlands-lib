import Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsStatement
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteSectionCover
import Langlands.AlgebraicGeometry.Picard.LineBundleDescent
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof
import Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proof: projective embeddings by sections from properness and ampleness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySections

variable {X : Scheme.{u}}

/-- A section trivializing a module on `U` is a frame on every smaller open. -/
lemma frame_of_trivializesOn (M : X.Modules) (s : GlobalSections M) {U : X.Opens}
    (h : TrivializesOn M s U) (V : X.Opens) (hV : V ≤ U) :
    Function.Bijective fun g : Γ(X, V) =>
      g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s : Γ(M, V)) := by
  have := (LineBundleDescent.trivializesOn_iff_bijective M s U).mp h V hV
  refine ⟨fun a b hab ↦ this.1 ?_, fun y ↦ ?_⟩
  · rw [LineBundleDescent.sectionHom_app, LineBundleDescent.sectionHom_app]
    exact hab
  · obtain ⟨g, hg⟩ := this.2 y
    exact ⟨g, (LineBundleDescent.sectionHom_app M s V g).symm.trans hg⟩

/-- An open on which a section is a frame lies in the section's generation open. -/
lemma le_trivializationOpen_of_frame (M : X.Modules) (s : GlobalSections M) (V : X.Opens)
    (h : ∀ W : X.Opens, W ≤ V → Function.Bijective fun g : Γ(X, W) =>
      g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(M, W))) :
    V ≤ trivializationOpen M s := by
  have ht : TrivializesOn M s V := by
    refine (LineBundleDescent.trivializesOn_iff_bijective M s V).mpr fun W hW ↦ ?_
    have hb := h W hW
    refine ⟨fun a b hab ↦ hb.1 ?_, fun y ↦ ?_⟩
    · exact (LineBundleDescent.sectionHom_app M s W a).symm.trans
        (hab.trans (LineBundleDescent.sectionHom_app M s W b))
    · obtain ⟨g, hg⟩ := hb.2 y
      exact ⟨g, (LineBundleDescent.sectionHom_app M s W g).trans hg⟩
  exact le_sSup ht

/-- Raising the exponent in a clearing identity by multiplying with the section. -/
lemma exists_clear_of_le (L : X.Modules) (s : GlobalSections L) (T : X.Opens) (r : Γ(X, T))
    (m₀ : ℕ) (a₀ : GlobalSections (tensorPow L m₀))
    (h₀ : (tensorPow L m₀).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op a₀ =
      r • (tensorPow L m₀).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op (sectionPow L s m₀))
    (m : ℕ) (hm : m₀ ≤ m) :
    ∃ a : GlobalSections (tensorPow L m),
      (tensorPow L m).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op a =
        r • (tensorPow L m).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op (sectionPow L s m) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨a₀, h₀⟩
  | succ n _ ih =>
    obtain ⟨a, ha⟩ := ih
    let μ := SectionClearing.sectionMul L s (tensorPow L n)
    refine ⟨μ.app ⊤ a, ?_⟩
    have h1 := SectionClearing.hom_app_map μ (le_top : T ≤ ⊤) a
    have h2 := SectionClearing.hom_app_map μ (le_top : T ≤ ⊤) (sectionPow L s n)
    rw [SectionClearing.sectionMul_app_sectionPow] at h2
    refine h1.symm.trans ?_
    rw [ha, Scheme.Modules.Hom.app_smul]
    exact congrArg (r • ·) h2

/-- A morphism with closed range is a closed immersion if it is one over each member of a
family of opens whose union contains its range. -/
lemma isClosedImmersion_of_restrict {Y : Scheme.{u}} (g : X ⟶ Y) (hc : IsClosed (Set.range g))
    {ι : Type*} (D : ι → Y.Opens) (hD : ∀ x : X, ∃ i, g x ∈ D i)
    (H : ∀ i, IsClosedImmersion (g ∣_ D i)) : IsClosedImmersion g := by
  let U : Option ι → Y.Opens := fun o ↦ o.elim ⟨(Set.range g)ᶜ, hc.isOpen_compl⟩ D
  apply IsZariskiLocalAtTarget.of_iSup_eq_top U
  · rw [eq_top_iff]
    intro y _
    by_cases hy : y ∈ Set.range g
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨i, hi⟩ := hD x
      exact Opens.mem_iSup.mpr ⟨some i, hi⟩
    · exact Opens.mem_iSup.mpr ⟨none, hy⟩
  · rintro (_ | i)
    · have : IsEmpty (g ⁻¹ᵁ U none).toScheme := ⟨fun z ↦ z.2 ⟨z.1, rfl⟩⟩
      infer_instance
    · exact H i

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate open `D₊(X t)` of the polynomial `Proj` projective space. -/
abbrev chart (R : Type u) [CommRing R] (N : ℕ) (t : Fin (N + 1)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X t)

/-- `appLE` only depends on the morphism, not on the proof of the inclusion. -/
lemma appLE_eq_of_eq {Y : Scheme.{u}} {g h : X ⟶ Y} (H : g = h) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ g ⁻¹ᵁ U) (e' : V ≤ h ⁻¹ᵁ U) : g.appLE U V e = h.appLE U V e' := by
  subst H
  rfl

/-- Composing with restriction along an equality of opens preserves surjectivity of `app`. -/
lemma surjective_app_comp_eqToHom {Y : Scheme.{u}} (g : X ⟶ Y) {U V : Y.Opens} (hUV : U = V)
    {A : X.Opens} (e : A = g ⁻¹ᵁ U) (hs : Function.Surjective (g.app V)) :
    Function.Surjective (g.app U ≫ X.presheaf.map (eqToHom e).op) := by
  subst hUV
  subst e
  simpa using hs

/-- On a coordinate chart whose preimage is affine and whose functions are generated by the
base and by ratios of the presentation's sections, the presentation's morphism is a closed
immersion over the chart. -/
lemma isClosedImmersion_restrict_chart {R : Type u} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (t : Fin (N + 1))
    (haff : IsAffineOpen (𝔓.toProj ⁻¹ᵁ chart R N t))
    (hgen : ∀ x : Γ(X, 𝔓.toProj ⁻¹ᵁ chart R N t), x ∈ Subring.closure
      (Set.range (f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ chart R N t) le_top) ∪
        {r | ∃ j, M.presheaf.map (homOfLE (le_top : 𝔓.toProj ⁻¹ᵁ chart R N t ≤ ⊤)).op (𝔓.σ j) =
          r • M.presheaf.map (homOfLE (le_top : 𝔓.toProj ⁻¹ᵁ chart R N t ≤ ⊤)).op (𝔓.σ t)})) :
    IsClosedImmersion (𝔓.toProj ∣_ chart R N t) := by
  have hχ : Function.Surjective (𝔓.toProj.app (chart R N t)) := by
    intro x
    refine (Subring.closure_le.mpr ?_ (hgen x) : x ∈ (𝔓.toProj.app (chart R N t)).hom.range)
    rintro _ (⟨a, rfl⟩ | ⟨j, hj⟩)
    · refine ⟨(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.map
        (homOfLE (le_top : chart R N t ≤ ⊤)).op ((ProjSpace.π R N).app ⊤ a), ?_⟩
      have e1 : f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ chart R N t) le_top =
          (ProjSpace.π R N).app ⊤ ≫ 𝔓.toProj.appLE _ (𝔓.toProj ⁻¹ᵁ chart R N t) le_top := by
        exact (appLE_eq_of_eq 𝔓.toProj_π.symm _ _ _ _).trans
          (Scheme.Hom.comp_appLE 𝔓.toProj (ProjSpace.π R N) ⊤ _ le_top)
      have e2 : 𝔓.toProj.appLE ((ProjSpace.π R N) ⁻¹ᵁ ⊤) (𝔓.toProj ⁻¹ᵁ chart R N t) le_top =
          (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.map
            (homOfLE (le_top : chart R N t ≤ ⊤)).op ≫ 𝔓.toProj.app (chart R N t) := by
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
        rfl
      rw [e1, e2]
      rfl
    · refine ⟨Proj.awayToSection _ (MvPolynomial.X t) (ProjSpace.ratio R N t j), ?_⟩
      apply (𝔓.frame t (𝔓.toProj ⁻¹ᵁ chart R N t) le_rfl).1
      exact (𝔓.app_ratio_smul t j).trans hj
  have : IsAffine (𝔓.toProj ⁻¹ᵁ chart R N t).toScheme := haff
  have : IsAffine (chart R N t).toScheme :=
    Proj.isAffineOpen_basicOpen _ _ (ProjSpace.X_mem_one R N t) one_pos
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [morphismRestrict_appTop]
  exact surjective_app_comp_eqToHom _ (Scheme.Opens.ι_image_top _) _ hχ

/-- On an affine open of a scheme locally of finite type over `Spec R`, finitely many functions
generate the ring of functions over the image of `R`. -/
lemma exists_generators {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] (T : X.Opens) (hT : IsAffineOpen T) :
    ∃ G : Finset Γ(X, T), ∀ x : Γ(X, T),
      x ∈ Subring.closure (Set.range (f.appLE ⊤ T le_top) ∪ (G : Set Γ(X, T))) := by
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_›
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ ⟨T, hT⟩ le_top
  let := (f.appLE ⊤ T le_top).hom.toAlgebra
  obtain ⟨G, hG⟩ := hft.out
  refine ⟨G, fun x ↦ ?_⟩
  have hx : x ∈ (Algebra.adjoin Γ(Spec (CommRingCat.of R), ⊤) (G : Set Γ(X, T))).toSubring := by
    rw [hG]
    trivial
  rw [Algebra.adjoin_eq_ring_closure] at hx
  exact hx

/-- Assembly: if the generation opens of some of the sections `σ` of one module are affine,
cover `X`, and have their functions generated by the base and by ratios of the sections, then
`f` has a closed projective embedding by sections. -/
theorem exists_closedImmersionBySections_of_sections {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (M : X.Modules) (N : ℕ)
    (σ : Fin (N + 1) → Γ(M, ⊤)) {I : Type*} (base : I → Fin (N + 1)) (T : I → X.Opens)
    (hT : ∀ i, trivializationOpen M (σ (base i)) = T i)
    (hcov : ∀ x : X, ∃ i, x ∈ T i)
    (haff : ∀ i, IsAffineOpen (T i))
    (hgen : ∀ i (x : Γ(X, T i)), x ∈ Subring.closure
      (Set.range (f.appLE ⊤ (T i) le_top) ∪
        {r | ∃ j, M.presheaf.map (homOfLE (le_top : T i ≤ ⊤)).op (σ j) =
          r • M.presheaf.map (homOfLE (le_top : T i ≤ ⊤)).op (σ (base i))})) :
    ∃ M' : X.Modules, Scheme.Modules.IsInvertible M' ∧
      Scheme.Modules.ClosedImmersionBySections M' f := by
  let U : Fin (N + 1) → X.Opens := fun t ↦ trivializationOpen M (σ t)
  have hU : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := hcov x
    rw [← hT i] at hi
    exact Opens.mem_iSup.mpr ⟨base i, hi⟩
  obtain ⟨𝔓, hσ, hle⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top f M N σ U hU
    (fun i V hV ↦ frame_of_trivializesOn M (σ i) (trivializesOn_trivializationOpen M (σ i)) V hV)
  have hP : ∀ t, 𝔓.toProj ⁻¹ᵁ chart R N t = U t := by
    intro t
    refine le_antisymm ?_ (hle t)
    refine le_trivializationOpen_of_frame M (σ t) _ fun W hW ↦ ?_
    have := 𝔓.frame t W hW
    rw [hσ] at this
    exact this
  have hP' : ∀ i, 𝔓.toProj ⁻¹ᵁ chart R N (base i) = T i := fun i ↦ (hP (base i)).trans (hT i)
  have hC : ∀ i, IsClosedImmersion (𝔓.toProj ∣_ chart R N (base i)) := by
    intro i
    apply isClosedImmersion_restrict_chart 𝔓 (base i)
    · rw [hP']
      exact haff i
    · rw [hP', hσ]
      exact hgen i
  have : IsSeparated (ProjSpace.π R N) :=
    inferInstanceAs (IsSeparated (projectiveSpaceToSpec R N))
  have : UniversallyClosed (𝔓.toProj ≫ ProjSpace.π R N) := by
    rw [𝔓.toProj_π]
    infer_instance
  have : UniversallyClosed 𝔓.toProj :=
    UniversallyClosed.of_comp_of_isSeparated _ (ProjSpace.π R N)
  have hcl : IsClosed (Set.range 𝔓.toProj) := 𝔓.toProj.isClosedMap.isClosed_range
  have : IsClosedImmersion 𝔓.toProj := by
    refine isClosedImmersion_of_restrict 𝔓.toProj hcl (fun i ↦ chart R N (base i))
      (fun x ↦ ?_) hC
    obtain ⟨i, hi⟩ := hcov x
    refine ⟨i, ?_⟩
    have : x ∈ 𝔓.toProj ⁻¹ᵁ chart R N (base i) := by
      rw [hP']
      exact hi
    exact this
  exact (exists_closedImmersionBySections_iff_isHProjective f).mpr
    ⟨N, 𝔓.toProj, this, 𝔓.toProj_π⟩

end Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySections

namespace Langlands.AlgebraicGeometry.Picard

open ProperAmpleClosedImmersionBySections in
/-- Proof of `ProperAmpleClosedImmersionBySectionsStatement`: a proper scheme over a noetherian
affine base with an ample line bundle has a closed projective embedding by sections. -/
theorem properAmpleClosedImmersionBySections :
    ProperAmpleClosedImmersionBySectionsStatement.{u} := by
  intro R _ _ X f hf ⟨L, hL⟩
  have : IsProper f := hf
  have : CompactSpace X := hL.compactSpace
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let C := hL.finiteAffinePowerSectionCover
  let L' : LineBundle X := ⟨tensorPow L.obj C.degree, tensorPow_isLocallyFreeRankOne X L C.degree⟩
  let s : Fin (C.dimension + 1) → GlobalSections L'.obj := C.sections
  let T : Fin (C.dimension + 1) → X.Opens := fun i ↦ trivializationOpen L'.obj (s i)
  have hTaff : ∀ i, IsAffineOpen (T i) := C.affine
  have hTcov : ∀ x : X, ∃ i, x ∈ T i := C.covers
  choose G hG using fun i ↦ exists_generators f (T i) (hTaff i)
  have hclear : ∀ i (r : G i), ∃ (m₀ : ℕ) (a₀ : GlobalSections (tensorPow L'.obj m₀)),
      (tensorPow L'.obj m₀).presheaf.map (homOfLE (le_top : T i ≤ ⊤)).op a₀ =
        r.1 • (tensorPow L'.obj m₀).presheaf.map (homOfLE (le_top : T i ≤ ⊤)).op
          (sectionPow L'.obj (s i) m₀) :=
    fun i r ↦ lineBundleSectionClearing X L' (s i) r.1
  choose m₀ a₀ ha₀ using hclear
  let m : ℕ := 1 + Finset.univ.sup (fun p : Σ i, G i ↦ m₀ p.1 p.2)
  have hm : ∀ i r, m₀ i r ≤ m := fun i r ↦ by
    have := Finset.le_sup (f := fun p : Σ i, G i ↦ m₀ p.1 p.2) (Finset.mem_univ ⟨i, r⟩)
    simp only at this
    omega
  have hmpos : 0 < m := by omega
  have hraise : ∀ i (r : G i), ∃ a : GlobalSections (tensorPow L'.obj m),
      (tensorPow L'.obj m).presheaf.map (homOfLE (le_top : T i ≤ ⊤)).op a =
        r.1 • (tensorPow L'.obj m).presheaf.map (homOfLE (le_top : T i ≤ ⊤)).op
          (sectionPow L'.obj (s i) m) :=
    fun i r ↦ exists_clear_of_le L'.obj (s i) (T i) r.1 (m₀ i r) (a₀ i r) (ha₀ i r) m (hm i r)
  choose a ha using hraise
  let J := Σ i : Fin (C.dimension + 1), Option (G i)
  let N := Fintype.card J - 1
  have hcard : Fintype.card J = N + 1 := by
    have : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨⟨0, none⟩⟩
    omega
  let e : J ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let M := tensorPow L'.obj m
  let σ0 : J → Γ(M, ⊤) := fun p ↦ match p with
    | ⟨i, none⟩ => sectionPow L'.obj (s i) m
    | ⟨i, some r⟩ => a i r
  let σ : Fin (N + 1) → Γ(M, ⊤) := fun t ↦ σ0 (e.symm t)
  let base : Fin (C.dimension + 1) → Fin (N + 1) := fun i ↦ e ⟨i, none⟩
  have hσb : ∀ i, σ (base i) = sectionPow L'.obj (s i) m := fun i ↦ by
    simp only [σ, base, Equiv.symm_apply_apply, σ0]
  have hσr : ∀ i r, σ (e ⟨i, some r⟩) = a i r := fun i r ↦ by
    simp only [σ, Equiv.symm_apply_apply, σ0]
  refine exists_closedImmersionBySections_of_sections f M N σ base T (fun i ↦ ?_) hTcov hTaff
    (fun i x ↦ ?_)
  · rw [hσb]
    exact trivializationOpen_sectionPow L' (s i) hmpos
  · refine Subring.closure_mono ?_ (hG i x)
    rintro y (hy | hy)
    · exact Or.inl hy
    · right
      refine ⟨e ⟨i, some ⟨y, hy⟩⟩, ?_⟩
      rw [hσr, hσb]
      exact ha i ⟨y, hy⟩

end Langlands.AlgebraicGeometry.Picard
