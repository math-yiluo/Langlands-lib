import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Picard.PrincipalLocalization
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit

/-!
# Local freeness of the closure of an invertible ideal

Let `j : Y ⟶ X` be an open immersion into a locally Noetherian scheme whose local rings at the
points outside the image are factorial, and let `s : D ⟶ 𝒪_Y` be a monomorphism from a locally
free sheaf of rank one. If a monomorphism `t : M ⟶ 𝒪_X` has as section image on each open `W`
exactly the functions whose image under `j` lies in the section image of `s`, then `M` is
locally free of rank one (`isLocallyFreeRankOne_of_range_iff`).

Near a point of the image a frame of `D` transports to a generator of the section image of `t`
(`exists_isFrameOn_of_mem_range`). Near a point `x` with factorial local ring, the section image
on an affine neighbourhood `V₀ = Spec A` is an intersection of finitely many saturations
`{c | ∃ N, aᵢ ^ N * c ∈ (δᵢ)}`, which becomes principal in the factorial local ring
(`exists_generator_near_prime`); a generator spreads to a basic open around `x`
(`exists_isFrameOn_of_factorial`). A section whose image generates the section image and is a
nonzerodivisor on small opens is a frame (`isFrameOn_of_locally_isGood`), hence a local
trivialization.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal

section Generic

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A monomorphism of scheme modules is injective on sections. -/
lemma app_injective_of_mono (φ : M ⟶ N) [Mono φ] (V : X.Opens) :
    Function.Injective (φ.app V) := by
  have : Mono φ.mapPresheaf := (Scheme.Modules.toPresheaf X).map_mono φ
  have : Mono (φ.mapPresheaf.app (op V)) := (NatTrans.mono_iff_mono_app _).1 this _
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- Sections of a morphism commute with restriction. -/
lemma app_map (φ : M ⟶ N) {V W : X.Opens} (i : W ⟶ V) (m : Γ(M, V)) :
    φ.app W (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app V m) := by
  have := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at this
  exact this

variable (t : M ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- The sections of a map into the structure module, as functions of the structure sheaf. -/
def secs (W : X.Opens) (m : Γ(M, W)) : Γ(X, W) := t.app W m

/-- The section map is linear over the structure sheaf. -/
lemma secs_smul (W : X.Opens) (g : Γ(X, W)) (m : Γ(M, W)) :
    secs t W (g • m) = g * secs t W m :=
  Scheme.Modules.Hom.app_smul t g m

/-- The section map commutes with restriction. -/
lemma secs_map {V W : X.Opens} (i : W ⟶ V) (m : Γ(M, V)) :
    secs t W (M.presheaf.map i.op m) = X.presheaf.map i.op (secs t V m) :=
  app_map t i m

/-- A monomorphism into the structure module is injective on sections. -/
lemma secs_injective [Mono t] (W : X.Opens) : Function.Injective (secs t W) :=
  app_injective_of_mono t W

end Generic

section Sheaf

variable {X : Scheme.{u}}

/-- Restrictions of functions compose. -/
lemma res_res {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (c : Γ(X, W)) :
    X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op c) =
      X.presheaf.map (homOfLE (h₁.trans h₂)).op c := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restrictions of module sections compose. -/
lemma mres_res (M : X.Modules) {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (m : Γ(M, W)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op m) =
      M.presheaf.map (homOfLE (h₁.trans h₂)).op m := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A function vanishing near every point vanishes. -/
lemma eq_zero_of_locally {W : X.Opens} (c : Γ(X, W))
    (h : ∀ y ∈ W, ∃ (W' : X.Opens) (hW' : W' ≤ W), y ∈ W' ∧
      X.presheaf.map (homOfLE hW').op c = 0) :
    c = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W c 0 fun y hy => ?_
  obtain ⟨W', hW', hy', h0⟩ := h y hy
  have h1 := X.presheaf.germ_res_apply (homOfLE hW') y hy' c
  rw [h0, map_zero] at h1
  rw [map_zero]
  exact h1.symm

/-- Functions agreeing near every point agree. -/
lemma eq_of_locally {W : X.Opens} (c c' : Γ(X, W))
    (h : ∀ y ∈ W, ∃ (W' : X.Opens) (hW' : W' ≤ W), y ∈ W' ∧
      X.presheaf.map (homOfLE hW').op c = X.presheaf.map (homOfLE hW').op c') :
    c = c' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_locally _ fun y hy => ?_
  obtain ⟨W', hW', hy', h0⟩ := h y hy
  exact ⟨W', hW', hy', by rw [map_sub, h0, sub_self]⟩

/-- Compatible local functions glue. -/
lemma exists_glue {W : X.Opens} (V : W → X.Opens) (hV : ∀ y : W, (y : X) ∈ V y)
    (hVW : ∀ y, V y ≤ W) (g : ∀ y, Γ(X, V y))
    (hg : ∀ y z, X.presheaf.map (homOfLE (inf_le_left : V y ⊓ V z ≤ V y)).op (g y) =
      X.presheaf.map (homOfLE (inf_le_right : V y ⊓ V z ≤ V z)).op (g z)) :
    ∃ c : Γ(X, W), ∀ y, X.presheaf.map (homOfLE (hVW y)).op c = g y := by
  obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' V W (fun y => homOfLE (hVW y))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV ⟨y, hy⟩⟩) g hg
  exact ⟨c, hc⟩

end Sheaf

section Frame

variable {X : Scheme.{u}} {M : X.Modules} (t : M ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- A section `f` on `W` is a nonzerodivisor generating the section range of `t` on `W`. -/
def IsGood (W : X.Opens) (f : Γ(X, W)) : Prop :=
  (∀ g : Γ(X, W), g * f = 0 → g = 0) ∧ ∀ m : Γ(M, W), ∃ g : Γ(X, W), secs t W m = g * f

/-- `ε` generates the section range of `t` and is a nonzerodivisor on every open of `O`. -/
def IsGenerator (O : X.Opens) (ε : Γ(X, O)) : Prop :=
  ∀ (W : X.Opens) (hWO : W ≤ O),
    (∀ c : Γ(X, W), (∃ m : Γ(M, W), secs t W m = c) ↔
      ∃ g : Γ(X, W), c = g * X.presheaf.map (homOfLE hWO).op ε) ∧
    ∀ g : Γ(X, W), g * X.presheaf.map (homOfLE hWO).op ε = 0 → g = 0

variable {t}

/-- A section of `M` whose image is good on arbitrarily small neighbourhoods is a frame. -/
theorem isFrameOn_of_locally_isGood [Mono t] {O : X.Opens} (σ : Γ(M, O))
    (hgood : ∀ W : X.Opens, W ≤ O → ∀ y ∈ W, ∃ (W' : X.Opens) (hW'O : W' ≤ O), W' ≤ W ∧ y ∈ W' ∧
      IsGood t W' (X.presheaf.map (homOfLE hW'O).op (secs t O σ))) :
    Scheme.Modules.IsFrameOn σ O := by
  set f := secs t O σ with hf
  -- the image of `σ` is a nonzerodivisor on every open of `O`
  have hnzd : ∀ (W : X.Opens) (hWO : W ≤ O) (g : Γ(X, W)),
      g * X.presheaf.map (homOfLE hWO).op f = 0 → g = 0 := by
    intro W hWO g hg
    refine eq_zero_of_locally g fun y hy => ?_
    obtain ⟨W', hW'O, hW'W, hy', hW'⟩ := hgood W hWO y hy
    refine ⟨W', hW'W, hy', hW'.1 _ ?_⟩
    have := congrArg (X.presheaf.map (homOfLE hW'W).op) hg
    rwa [map_mul, res_res, map_zero] at this
  intro W hWU hWV
  have hsecs : ∀ g : Γ(X, W), secs t W (g • M.presheaf.map (homOfLE hWU).op σ) =
      g * X.presheaf.map (homOfLE hWU).op f := by
    intro g
    rw [secs_smul, secs_map]
  constructor
  · intro g g' hgg'
    have := congrArg (secs t W) hgg'
    simp only [hsecs] at this
    rw [← sub_eq_zero]
    exact hnzd W hWU _ (by rw [sub_mul, this, sub_self])
  · intro m
    have hloc : ∀ y : W, ∃ (W' : X.Opens) (hW'O : W' ≤ O) (hW'W : W' ≤ W), (y : X) ∈ W' ∧
        ∃ g : Γ(X, W'), secs t W' (M.presheaf.map (homOfLE hW'W).op m) =
          g * X.presheaf.map (homOfLE hW'O).op f := by
      intro y
      obtain ⟨W', hW'O, hW'W, hy', hW'⟩ := hgood W hWU y y.2
      exact ⟨W', hW'O, hW'W, hy', hW'.2 _⟩
    choose V hVO hVW hyV g hg using hloc
    obtain ⟨c, hc⟩ := exists_glue V hyV hVW g fun y z => by
      have hyz : V y ⊓ V z ≤ O := inf_le_left.trans (hVO y)
      rw [← sub_eq_zero]
      apply hnzd _ hyz
      have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : V y ⊓ V z ≤ V y)).op) (hg y)
      have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : V y ⊓ V z ≤ V z)).op) (hg z)
      rw [← secs_map, mres_res, map_mul, res_res] at e1 e2
      rw [sub_mul, sub_eq_zero]
      exact e1.symm.trans e2
    refine ⟨c, secs_injective t W ?_⟩
    rw [hsecs]
    refine eq_of_locally _ _ fun y hy => ⟨V ⟨y, hy⟩, hVW _, hyV _, ?_⟩
    rw [map_mul, res_res, hc, ← secs_map t (homOfLE (hVW ⟨y, hy⟩)) m, hg]

/-- A generator of the section range on every smaller open gives a frame. -/
theorem exists_isFrameOn_of_generator [Mono t] {O : X.Opens} (ε : Γ(X, O))
    (hε : IsGenerator t O ε) :
    ∃ σ : Γ(M, O), Scheme.Modules.IsFrameOn σ O := by
  obtain ⟨σ, hσ⟩ := ((hε O le_rfl).1 (X.presheaf.map (homOfLE le_rfl).op ε)).2
    ⟨1, (one_mul _).symm⟩
  refine ⟨σ, isFrameOn_of_locally_isGood (t := t) σ fun W hWO y hy => ⟨W, hWO, le_rfl, hy, ?_⟩⟩
  rw [hσ, res_res]
  refine ⟨(hε W hWO).2, fun m => ((hε W hWO).1 _).1 ⟨m, rfl⟩⟩

/-- A frame on an open neighbourhood gives a local trivialization. -/
lemma exists_restrict_iso_of_isFrameOn {L : X.Modules} {O : X.Opens} {σ : Γ(L, O)}
    (h : Scheme.Modules.IsFrameOn σ O) {x : X} (hx : x ∈ O) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty (L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :=
  ⟨O, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback O.ι).app L ≪≫
    (h.nonempty_pullback_iso_unit O le_rfl le_rfl).some⟩⟩

/-- A locally free sheaf of rank one has a frame near every point. -/
lemma exists_isFrameOn_of_isLocallyFreeRankOne {L : X.Modules} (hL : IsLocallyFreeRankOne L)
    (x : X) : ∃ (T : X.Opens) (_ : x ∈ T) (e : Γ(L, T)), Scheme.Modules.IsFrameOn e T := by
  obtain ⟨T, hxT, ⟨eT⟩⟩ := hL x
  obtain ⟨e, he⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit T
    (((Scheme.Modules.restrictFunctorIsoPullback T.ι).app L).symm ≪≫ eT)
  exact ⟨T, hxT, e, he⟩

end Frame

section OpenPart

variable {X Y : Scheme.{u}} (j : Y ⟶ X)

/-- The comorphism of a scheme morphism commutes with restriction. -/
lemma app_res {V W : X.Opens} (h : W ≤ V) (c : Γ(X, V)) :
    j.app W (X.presheaf.map (homOfLE h).op c) =
      Y.presheaf.map (homOfLE (fun _ hx => h hx : j ⁻¹ᵁ W ≤ j ⁻¹ᵁ V)).op (j.app V c) := by
  have := ConcreteCategory.congr_hom (j.naturality (homOfLE h).op) c
  simp only [ConcreteCategory.comp_apply] at this
  exact this

variable [IsOpenImmersion j]

/-- An open immersion is bijective on functions over opens of its image. -/
lemma app_bijective {W : X.Opens} (hW : W ≤ j.opensRange) : Function.Bijective (j.app W) := by
  have := j.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso _

variable {D : Y.Modules} (s : D ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono s]
  {M : X.Modules} (t : M ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- On an open of the image carrying a frame of `D`, the section range of `t` is principal. -/
theorem exists_generator_of_isFrameOn
    (ht : ∀ (W : X.Opens) (c : Γ(X, W)),
      (∃ m : Γ(M, W), t.app W m = c) ↔ ∃ d : Γ(D, j ⁻¹ᵁ W), s.app (j ⁻¹ᵁ W) d = j.app W c)
    {O : X.Opens} (hO : O ≤ j.opensRange) (e : Γ(D, j ⁻¹ᵁ O))
    (he : Scheme.Modules.IsFrameOn e (j ⁻¹ᵁ O)) :
    ∃ ε : Γ(X, O), IsGenerator t O ε := by
  obtain ⟨ε, hε⟩ := (app_bijective j hO).2 (secs s (j ⁻¹ᵁ O) e)
  refine ⟨ε, fun W hWO => ?_⟩
  have hWr : W ≤ j.opensRange := hWO.trans hO
  have hpre : j ⁻¹ᵁ W ≤ j ⁻¹ᵁ O := fun _ hx => hWO hx
  -- the image of the restricted generator
  have hjε : j.app W (X.presheaf.map (homOfLE hWO).op ε) =
      secs s (j ⁻¹ᵁ W) (D.presheaf.map (homOfLE hpre).op e) := by
    rw [app_res, hε, secs_map]
  have hsmul : ∀ g : Γ(X, W), j.app W (g * X.presheaf.map (homOfLE hWO).op ε) =
      secs s (j ⁻¹ᵁ W) (j.app W g • D.presheaf.map (homOfLE hpre).op e) := by
    intro g
    rw [map_mul, hjε, secs_smul]
  refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨d, hd⟩ := (ht W (secs t W m)).1 ⟨m, rfl⟩
    obtain ⟨h, rfl⟩ := (he hpre hpre).2 d
    obtain ⟨g, rfl⟩ := (app_bijective j hWr).2 h
    refine ⟨g, (app_bijective j hWr).1 ?_⟩
    rw [hsmul]
    exact hd.symm
  · rintro ⟨g, rfl⟩
    exact (ht W _).2 ⟨_, (hsmul g).symm⟩
  · intro g hg
    have h0 := hsmul g
    rw [hg, map_zero] at h0
    have h1 : j.app W g • D.presheaf.map (homOfLE hpre).op e = 0 :=
      secs_injective s _ (h0.symm.trans (map_zero _).symm)
    have h2 := (he.smul_eq_zero_iff hpre hpre (j.app W g)).1 h1
    exact (app_bijective j hWr).1 (h2.trans (map_zero _).symm)

/-- Near a point of the open image, `M` has a frame. -/
theorem exists_isFrameOn_of_mem_range [Mono t] (hD : IsLocallyFreeRankOne D)
    (ht : ∀ (W : X.Opens) (c : Γ(X, W)),
      (∃ m : Γ(M, W), t.app W m = c) ↔ ∃ d : Γ(D, j ⁻¹ᵁ W), s.app (j ⁻¹ᵁ W) d = j.app W c)
    {x : X} (hx : x ∈ Set.range j) :
    ∃ (O : X.Opens) (_ : x ∈ O) (σ : Γ(M, O)), Scheme.Modules.IsFrameOn σ O := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨T, hzT, e₀, he₀⟩ := exists_isFrameOn_of_isLocallyFreeRankOne hD z
  have hpre : j ⁻¹ᵁ (j ''ᵁ T) ≤ T := (j.preimage_image_eq T).le
  obtain ⟨ε, hε⟩ := exists_generator_of_isFrameOn j s t ht (j.image_le_opensRange T)
    (D.presheaf.map (homOfLE hpre).op e₀) ((he₀.map (homOfLE hpre)).mono hpre)
  obtain ⟨σ, hσ⟩ := exists_isFrameOn_of_generator ε hε
  exact ⟨j ''ᵁ T, Set.mem_image_of_mem _ hzT, σ, hσ⟩

end OpenPart

section Algebra

section Factorial

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- In a factorial domain, a nonzero `d` splits as a factor prime to `a` times a factor
dividing a power of `a`. -/
lemma exists_split (a d : R) (hd : d ≠ 0) :
    ∃ φ ψ : R, d = φ * ψ ∧ IsRelPrime φ a ∧ ∃ N : ℕ, ψ ∣ a ^ N := by
  revert hd
  refine UniqueFactorizationMonoid.induction_on_prime d ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _
    exact ⟨x, 1, (mul_one x).symm, hx.isRelPrime_left, 0, by simp⟩
  · intro b p hb hp ih _
    obtain ⟨φ, ψ, rfl, hrel, N, hN⟩ := ih hb
    by_cases hpa : p ∣ a
    · exact ⟨φ, p * ψ, by ring, hrel, N + 1, by rw [pow_succ']; exact mul_dvd_mul hpa hN⟩
    · exact ⟨p * φ, ψ, by ring, (hp.irreducible.isRelPrime_iff_not_dvd.2 hpa).mul_left hrel,
        N, hN⟩

/-- In a factorial domain, the saturation of a principal ideal by an element is principal. -/
lemma exists_dvd_iff (a δ : R) (hδ : δ = 0 → a = 0) :
    ∃ φ : R, φ ≠ 0 ∧ ∀ r : R, (∃ N : ℕ, δ ∣ a ^ N * r) ↔ φ ∣ r := by
  by_cases hδ0 : δ = 0
  · refine ⟨1, one_ne_zero, fun r => ⟨fun _ => one_dvd r, fun _ => ⟨1, ?_⟩⟩⟩
    rw [hδ0, hδ hδ0, pow_one, zero_mul]
  · obtain ⟨φ, ψ, rfl, hrel, N, hN⟩ := exists_split a δ hδ0
    refine ⟨φ, left_ne_zero_of_mul hδ0, fun r => ⟨?_, ?_⟩⟩
    · rintro ⟨n, hn⟩
      exact hrel.pow_right.dvd_of_dvd_mul_left ((dvd_mul_right φ ψ).trans hn)
    · rintro ⟨u, rfl⟩
      obtain ⟨k, hk⟩ := hN
      exact ⟨N, k * u, by rw [hk]; ring⟩

/-- In a factorial domain, finitely many nonzero elements have a nonzero least common
multiple. -/
lemma exists_lcm {ι : Type*} (T : Finset ι) (φ : ι → R) (hφ : ∀ k ∈ T, φ k ≠ 0) :
    ∃ Φ : R, Φ ≠ 0 ∧ ∀ r : R, (∀ k ∈ T, φ k ∣ r) ↔ Φ ∣ r := by
  classical
  let := UniqueFactorizationMonoid.toGCDMonoid R
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun r => by simp⟩
  | insert k T hk ih =>
    obtain ⟨Φ, hΦ, hΦr⟩ := ih fun i hi => hφ i (Finset.mem_insert_of_mem hi)
    refine ⟨lcm (φ k) Φ, ?_, fun r => ?_⟩
    · rw [Ne, lcm_eq_zero_iff, not_or]
      exact ⟨hφ k (Finset.mem_insert_self k T), hΦ⟩
    · rw [lcm_dvd_iff, ← hΦr, Finset.forall_mem_insert]

end Factorial

variable {A : Type*} [CommRing A]

/-- The saturation `{c | ∃ N, a ^ N * c ∈ (δ)}` of a principal ideal. -/
def satIdeal (a δ : A) : Ideal A where
  carrier := {c | ∃ N : ℕ, a ^ N * c ∈ Ideal.span {δ}}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro c c' ⟨N, hN⟩ ⟨N', hN'⟩
    refine ⟨N + N', ?_⟩
    have : a ^ (N + N') * (c + c') = a ^ N' * (a ^ N * c) + a ^ N * (a ^ N' * c') := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hN) (Ideal.mul_mem_left _ _ hN')
  smul_mem' := by
    rintro r c ⟨N, hN⟩
    refine ⟨N, ?_⟩
    have : a ^ N * (r • c) = r * (a ^ N * c) := by rw [smul_eq_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hN

/-- Membership in a saturation. -/
lemma mem_satIdeal {a δ c : A} : c ∈ satIdeal a δ ↔ ∃ N : ℕ, a ^ N * c ∈ Ideal.span {δ} :=
  Iff.rfl

variable [IsNoetherianRing A] (P : Ideal A) [P.IsPrime]
  (R : Type*) [CommRing R] [Algebra A R] [IsLocalization.AtPrime R P]
  [UniqueFactorizationMonoid R]

include R in
/-- A finite intersection of saturated principal ideals is principal at a factorial prime,
with a generator that is a nonzerodivisor near the prime. -/
theorem exists_generator_near_prime {ι : Type*} (T : Finset ι) (a δ : ι → A)
    (hδ : ∀ k ∈ T, ∀ h : A, δ k * h = 0 → ∃ N : ℕ, a k ^ N * h = 0) :
    ∃ f : A, (∀ k ∈ T, ∃ N : ℕ, a k ^ N * f ∈ Ideal.span {δ k}) ∧ ∃ g ∉ P,
      (∀ c : A, (∀ k ∈ T, ∃ N : ℕ, a k ^ N * c ∈ Ideal.span {δ k}) →
        g * c ∈ Ideal.span {f}) ∧
      ∀ h : A, f * h = 0 → g * h = 0 := by
  classical
  have := IsLocalization.AtPrime.isLocalRing R P
  have : IsDomain R := {}
  let I : Ideal A := ⨅ k ∈ T, satIdeal (a k) (δ k)
  have hI : ∀ c, c ∈ I ↔ ∀ k ∈ T, ∃ N : ℕ, a k ^ N * c ∈ Ideal.span {δ k} := by
    intro c
    simp only [I, Submodule.mem_iInf, mem_satIdeal]
  -- the local generators of the saturations
  have hloc : ∀ k ∈ T, ∃ φ : R, φ ≠ 0 ∧ ∀ r : R,
      (∃ N : ℕ, algebraMap A R (δ k) ∣ algebraMap A R (a k) ^ N * r) ↔ φ ∣ r := by
    intro k hk
    refine exists_dvd_iff _ _ fun h0 => ?_
    obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl R _).1 h0
    obtain ⟨N, hN⟩ := hδ k hk u (by rw [mul_comm]; exact hu)
    have h1 := congrArg (algebraMap A R) hN
    rw [map_mul, map_pow, map_zero] at h1
    have hu' := IsLocalization.map_units R u
    exact eq_zero_of_pow_eq_zero (hu'.mul_left_eq_zero.1 h1)
  choose! φ hφ0 hφ using hloc
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_lcm T φ hφ0
  -- membership in `I` is detected by divisibility by `Φ` in `R`
  have hmem : ∀ c ∈ I, Φ ∣ algebraMap A R c := by
    intro c hc
    refine (hΦ _).1 fun k hk => (hφ k hk _).1 ?_
    obtain ⟨N, hN⟩ := (hI c).1 hc k hk
    have h1 := map_dvd (algebraMap A R) (Ideal.mem_span_singleton.1 hN)
    rw [map_mul, map_pow] at h1
    exact ⟨N, h1⟩
  have hgen : Φ ∈ I.map (algebraMap A R) := by
    obtain ⟨⟨c₀, s₀⟩, hcs⟩ := IsLocalization.surj P.primeCompl Φ
    have hc₀ : ∀ k ∈ T, ∃ w ∈ P.primeCompl, ∃ N : ℕ,
        a k ^ N * (w * c₀) ∈ Ideal.span {δ k} := by
      intro k hk
      obtain ⟨N, hN⟩ := (hφ k hk _).2 (((hΦ Φ).2 dvd_rfl k hk).trans ⟨_, hcs.symm⟩)
      have hN' : algebraMap A R (a k ^ N * c₀) ∈ (Ideal.span {δ k}).map (algebraMap A R) := by
        rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, map_mul, map_pow]
        exact hN
      obtain ⟨w, hw, hwc⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl R _ _).1 hN'
      exact ⟨w, hw, N, by rw [mul_left_comm]; exact hwc⟩
    choose! w hw N hN using hc₀
    have hW : ∏ k ∈ T, w k ∈ P.primeCompl := prod_mem fun k hk => hw k hk
    have hWc : (∏ k ∈ T, w k) * c₀ ∈ I := by
      refine (hI _).2 fun k hk => ⟨N k, ?_⟩
      obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem w hk
      rw [he, show a k ^ N k * (w k * e * c₀) = e * (a k ^ N k * (w k * c₀)) by ring]
      exact Ideal.mul_mem_left _ _ (hN k hk)
    refine (IsLocalization.mem_map_algebraMap_iff P.primeCompl R).2
      ⟨⟨⟨_, hWc⟩, ⟨_, P.primeCompl.mul_mem hW s₀.2⟩⟩, ?_⟩
    simp only [map_mul]
    rw [← hcs]
    ring
  have hspan : I.map (algebraMap A R) = Ideal.span {Φ} := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact hmem c hc
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hgen
  obtain ⟨f, hfI, hf⟩ := PrimeDivisor.exists_numerator_generator P.primeCompl R I ⟨⟨Φ, hspan⟩⟩
  have hf0 : algebraMap A R f ≠ 0 := by
    intro h0
    apply hΦ0
    refine Ideal.span_singleton_eq_bot.1 ((hspan.symm.trans hf).trans ?_)
    rw [h0]
    exact Ideal.span_singleton_eq_bot.2 rfl
  obtain ⟨g₁, hg₁, hg₁I⟩ := PrimeDivisor.exists_denominator_of_map_le P.primeCompl R I
    (Ideal.span {f}) (IsNoetherian.noetherian I)
    (by rw [hf, Ideal.map_span, Set.image_singleton])
  let K : Ideal A := (⊥ : Ideal A).colon (Ideal.span {f})
  have hK : ∀ h, h ∈ K ↔ h * f = 0 := by
    intro h
    simp only [K, Ideal.mem_colon_span_singleton, Ideal.mem_bot]
  obtain ⟨g₂, hg₂, hg₂K⟩ := PrimeDivisor.exists_denominator_of_map_le P.primeCompl R K ⊥
    (IsNoetherian.noetherian K) (by
      rw [Ideal.map_bot, Ideal.map_le_iff_le_comap]
      intro h hh
      rw [Ideal.mem_comap, Ideal.mem_bot]
      have := congrArg (algebraMap A R) ((hK h).1 hh)
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hf0)
  refine ⟨f, (hI f).1 hfI, g₁ * g₂, P.primeCompl.mul_mem hg₁ hg₂, fun c hc => ?_, fun h hh => ?_⟩
  · rw [mul_comm g₁, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hg₁I c ((hI c).2 hc))
  · have := hg₂K h ((hK h).2 (by rw [mul_comm]; exact hh))
    rw [Ideal.mem_bot] at this
    rw [mul_comm g₁, mul_assoc, mul_comm g₁, ← mul_assoc, this, zero_mul]

end Algebra

section Complement

section Helpers

variable {X Y : Scheme.{u}}

/-- Restriction to the same open is the identity. -/
lemma res_self {W : X.Opens} (c : Γ(X, W)) : X.presheaf.map (homOfLE (le_refl W)).op c = c := by
  rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- A section is a unit on every open inside its basic open. -/
lemma isUnit_res_of_le_basicOpen {U W : X.Opens} (g : Γ(X, U)) (hWU : W ≤ U)
    (hW : W ≤ X.basicOpen g) : IsUnit (X.presheaf.map (homOfLE hWU).op g) := by
  apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace W
  intro y hy
  have h1 := X.presheaf.germ_res_apply (homOfLE hWU) y hy g
  change IsUnit (X.presheaf.germ W y hy (X.presheaf.map (homOfLE hWU).op g))
  rw [h1]
  exact (Scheme.mem_basicOpen X g y (hWU hy)).1 (hW hy)

/-- Points of a basic open of an affine open are the primes avoiding the section. -/
lemma mem_basicOpen_iff {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {x : X} (hx : x ∈ V₀)
    (g : Γ(X, V₀)) : x ∈ X.basicOpen g ↔ g ∉ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hV₀.fromSpec_preimage_basicOpen]
  change x ∈ X.basicOpen g ↔ hV₀.fromSpec (hV₀.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen g
  rw [hV₀.fromSpec_primeIdealOf]

/-- The algebra structure on a basic open is restriction. -/
lemma algebraMap_basicOpen {V₀ : X.Opens} (b c : Γ(X, V₀)) :
    algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) c =
      X.presheaf.map (homOfLE (X.basicOpen_le b)).op c := rfl

variable {D : Y.Modules} (s : D ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono s]

/-- The section range of a monomorphism into the structure module is local. -/
lemma exists_secs_eq_of_locally {V : Y.Opens} (c : Γ(Y, V))
    (h : ∀ z ∈ V, ∃ (V' : Y.Opens) (hV' : V' ≤ V), z ∈ V' ∧
      ∃ d : Γ(D, V'), secs s V' d = Y.presheaf.map (homOfLE hV').op c) :
    ∃ d : Γ(D, V), secs s V d = c := by
  choose U hUV hzU d hd using fun z : V => h z z.2
  let F : TopCat.Sheaf Ab Y := ⟨D.presheaf, D.isSheaf⟩
  obtain ⟨e, he, -⟩ := F.existsUnique_gluing' U V (fun z => homOfLE (hUV z))
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩) d (fun y z => by
      apply secs_injective s
      change secs s _ (D.presheaf.map (homOfLE inf_le_left).op (d y)) =
        secs s _ (D.presheaf.map (homOfLE inf_le_right).op (d z))
      rw [secs_map, secs_map, hd, hd, res_res, res_res])
  refine ⟨e, eq_of_locally _ _ fun z hz => ⟨U ⟨z, hz⟩, hUV _, hzU _, ?_⟩⟩
  rw [← secs_map, he, hd]

end Helpers

/-- One power of `b` clears all the exponents of a finite family of saturations. -/
lemma exists_pow_mem_sat {A ι : Type*} [CommRing A] (T : Finset ι) (a δ : ι → A) (b c : A)
    (h : ∀ i ∈ T, ∃ n : ℕ, (b * a i) ^ n * c ∈ Ideal.span {δ i}) :
    ∃ N : ℕ, ∀ i ∈ T, ∃ n : ℕ, a i ^ n * (b ^ N * c) ∈ Ideal.span {δ i} := by
  classical
  choose! n hn using h
  refine ⟨∑ i ∈ T, n i, fun i hi => ⟨n i, ?_⟩⟩
  have hle : n i ≤ ∑ k ∈ T, n k := Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) hi
  rw [← pow_mul_pow_sub b hle,
    show a i ^ n i * (b ^ n i * b ^ (∑ k ∈ T, n k - n i) * c) =
      b ^ (∑ k ∈ T, n k - n i) * ((b * a i) ^ n i * c) by rw [mul_pow]; ring]
  exact Ideal.mul_mem_left _ _ (hn i hi)

section Cover

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  {D : Y.Modules} (s : D ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono s]
  {M : X.Modules} (t : M ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- Over an affine open of a locally Noetherian scheme, finitely many basic opens inside the
image carry generators of the section range and cover the image. -/
lemma exists_finite_generators [IsLocallyNoetherian X] (hD : IsLocallyFreeRankOne D)
    (ht : ∀ (W : X.Opens) (c : Γ(X, W)),
      (∃ m : Γ(M, W), t.app W m = c) ↔ ∃ d : Γ(D, j ⁻¹ᵁ W), s.app (j ⁻¹ᵁ W) d = j.app W c)
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) :
    ∃ (T : Finset (j ⁻¹ᵁ V₀)) (a : j ⁻¹ᵁ V₀ → Γ(X, V₀))
      (ε : ∀ i, Γ(X, X.basicOpen (a i))),
      (∀ i, IsGenerator t (X.basicOpen (a i)) (ε i)) ∧
      ∀ z : Y, j z ∈ V₀ → ∃ i ∈ T, j z ∈ X.basicOpen (a i) := by
  have hfr : ∀ i : j ⁻¹ᵁ V₀, ∃ a : Γ(X, V₀), j i.1 ∈ X.basicOpen a ∧
      ∃ ε, IsGenerator t (X.basicOpen a) ε := by
    rintro ⟨z, hz⟩
    obtain ⟨T, hzT, e₀, he₀⟩ := exists_isFrameOn_of_isLocallyFreeRankOne hD z
    obtain ⟨a, haT, hza⟩ :=
      hV₀.exists_basicOpen_le (V := j ''ᵁ T) ⟨j z, Set.mem_image_of_mem _ hzT⟩ hz
    have hO : X.basicOpen a ≤ j.opensRange := haT.trans (j.image_le_opensRange T)
    have hpre : j ⁻¹ᵁ X.basicOpen a ≤ T := fun y hy => (j.preimage_image_eq T).le (haT hy)
    obtain ⟨ε, hε⟩ := exists_generator_of_isFrameOn j s t ht hO
      (D.presheaf.map (homOfLE hpre).op e₀) ((he₀.map (homOfLE hpre)).mono hpre)
    exact ⟨a, hza, ε, hε⟩
  choose a ha ε hε using hfr
  have hcpt : IsCompact (j ⁻¹ᵁ V₀ : Set Y) := j.isCompact_preimage hV₀.isCompact
  obtain ⟨T, hT⟩ := hcpt.elim_finite_subcover (fun i => (j ⁻¹ᵁ X.basicOpen (a i) : Set Y))
    (fun i => (j ⁻¹ᵁ X.basicOpen (a i)).isOpen)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, ha ⟨z, hz⟩⟩)
  refine ⟨T, a, ε, hε, fun z hz => ?_⟩
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (hT hz)
  exact ⟨i, hi, hzi⟩

end Cover


section Factorial

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  {D : Y.Modules} (s : D ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono s]
  {M : X.Modules} (t : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono t]

/-- Near a point with factorial local ring, `M` has a frame. -/
theorem exists_isFrameOn_of_factorial [IsLocallyNoetherian X] (hD : IsLocallyFreeRankOne D)
    (ht : ∀ (W : X.Opens) (c : Γ(X, W)),
      (∃ m : Γ(M, W), t.app W m = c) ↔ ∃ d : Γ(D, j ⁻¹ᵁ W), s.app (j ⁻¹ᵁ W) d = j.app W c)
    (x : X) (hx : UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ (O : X.Opens) (_ : x ∈ O) (σ : Γ(M, O)), Scheme.Modules.IsFrameOn σ O := by
  obtain ⟨V₀, hV₀, hxV₀, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  replace hV₀ : IsAffineOpen V₀ := hV₀
  have : IsNoetherianRing Γ(X, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  let P := (hV₀.primeIdealOf ⟨x, hxV₀⟩).asIdeal
  let _ : Algebra Γ(X, V₀) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV₀⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) P := hV₀.isLocalization_stalk ⟨x, hxV₀⟩
  obtain ⟨T, a, ε, hε, hcov⟩ := exists_finite_generators j s t hD ht hV₀
  have hloc : ∀ b : Γ(X, V₀), IsLocalization.Away b Γ(X, X.basicOpen b) :=
    fun b => hV₀.isLocalization_basicOpen b
  -- numerators of the local generators
  have hnum : ∀ i, ∃ (m : ℕ) (δ : Γ(X, V₀)),
      ε i * algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) (a i) ^ m =
        algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) δ := fun i => by
    have := hloc (a i)
    exact IsLocalization.Away.surj (a i) (ε i)
  choose m δ hδε using hnum
  have hδ : ∀ i ∈ T, ∀ h : Γ(X, V₀), δ i * h = 0 → ∃ N : ℕ, a i ^ N * h = 0 := by
    intro i _ h hh
    have := hloc (a i)
    have h1 : (algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) (a i) ^ m i *
        algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) h) * ε i = 0 := by
      rw [mul_comm, ← mul_assoc, hδε, ← map_mul, hh, map_zero]
    have h2 := (hε i _ le_rfl).2 (algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) (a i) ^ m i *
        algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) h) (by rw [res_self]; exact h1)
    rw [(IsLocalization.Away.algebraMap_pow_isUnit (a i) (m i)).mul_right_eq_zero] at h2
    obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (a i) (h2.trans (map_zero _).symm)
    exact ⟨N, by rw [hN, mul_zero]⟩
  obtain ⟨f, hfI, g, hgP, hgI, hgann⟩ :=
    exists_generator_near_prime P (X.presheaf.stalk x) T a δ hδ
  have hgV : X.basicOpen g ≤ V₀ := X.basicOpen_le g
  have hxO : x ∈ X.basicOpen g := (mem_basicOpen_iff hV₀ hxV₀ g).2 hgP
  -- `f` lies in the section range on `V₀`
  have hfr : ∃ σ₀ : Γ(M, V₀), secs t V₀ σ₀ = f := by
    refine (ht V₀ f).2 (exists_secs_eq_of_locally s _ fun z hz => ?_)
    obtain ⟨i, hi, hzi⟩ := hcov z hz
    have hiV : X.basicOpen (a i) ≤ V₀ := X.basicOpen_le (a i)
    refine ⟨j ⁻¹ᵁ X.basicOpen (a i), fun y hy => hiV hy, hzi, ?_⟩
    rw [← app_res j hiV f]
    refine (ht _ _).1 ?_
    obtain ⟨N, hN⟩ := hfI i hi
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 hN
    have := hloc (a i)
    obtain ⟨U, hUe⟩ :=
      IsLocalization.Away.algebraMap_pow_isUnit (S := Γ(X, X.basicOpen (a i))) (a i) N
    refine ((hε i _ le_rfl).1 _).2 ⟨↑U⁻¹ * (algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) q *
      algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) (a i) ^ m i), ?_⟩
    rw [res_self]
    change algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) f = _
    calc algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) f
        = ↑U⁻¹ * (↑U * algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) f) := by
          rw [Units.inv_mul_cancel_left]
      _ = ↑U⁻¹ * (algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) q *
          algebraMap Γ(X, V₀) Γ(X, X.basicOpen (a i)) (δ i)) := by
          rw [hUe, ← map_pow, ← map_mul, ← hq, map_mul]
      _ = _ := by rw [← hδε]; ring
  obtain ⟨σ₀, hσ₀⟩ := hfr
  refine ⟨X.basicOpen g, hxO, M.presheaf.map (homOfLE hgV).op σ₀,
    isFrameOn_of_locally_isGood (t := t) _ fun W hWO y hy => ?_⟩
  obtain ⟨b, hbW, hyb⟩ := hV₀.exists_basicOpen_le ⟨y, hy⟩ (hgV (hWO hy))
  have hbO : X.basicOpen b ≤ X.basicOpen g := hbW.trans hWO
  refine ⟨X.basicOpen b, hbO, hbW, hyb, ?_⟩
  rw [secs_map, hσ₀, res_res]
  change IsGood t (X.basicOpen b) (algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) f)
  have := hloc b
  have hgb : IsUnit (algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) g) :=
    isUnit_res_of_le_basicOpen g _ hbO
  have hbu : IsUnit (algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) b) :=
    IsLocalization.Away.algebraMap_isUnit b
  constructor
  · intro h hh
    obtain ⟨n, h₀, hh₀⟩ := IsLocalization.Away.surj b h
    have h1 : algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) (h₀ * f) =
        algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) 0 := by
      rw [map_mul, ← hh₀, mul_right_comm, hh, zero_mul, map_zero]
    obtain ⟨r, hr⟩ := IsLocalization.Away.exists_of_eq b h1
    rw [mul_zero] at hr
    have h2 := hgann (b ^ r * h₀) (by rw [← hr]; ring)
    have h3 := congrArg (algebraMap Γ(X, V₀) Γ(X, X.basicOpen b)) h2
    rw [map_mul, map_mul, map_pow, map_zero, ← hh₀] at h3
    have h4 : (algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) g *
        algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) b ^ r *
        algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) b ^ n) * h = 0 := by
      rw [← h3]; ring
    exact (((hgb.mul (hbu.pow r)).mul (hbu.pow n)).mul_right_eq_zero).1 h4
  · intro m'
    obtain ⟨n, c₀, hc₀⟩ := IsLocalization.Away.surj b (secs t (X.basicOpen b) m')
    have hm₀ : secs t (X.basicOpen b) (algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) b ^ n • m') =
        algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) c₀ := by
      rw [secs_smul, ← hc₀, mul_comm]
    -- saturation exponents
    have hsat : ∀ i ∈ T, ∃ k : ℕ, (b * a i) ^ k * c₀ ∈ Ideal.span {δ i} := by
      intro i _
      have hW : X.basicOpen (b * a i) ≤ X.basicOpen (a i) := by
        rw [Scheme.basicOpen_mul]; exact inf_le_right
      have hWb : X.basicOpen (b * a i) ≤ X.basicOpen b := by
        rw [Scheme.basicOpen_mul]; exact inf_le_left
      have := hloc (b * a i)
      have hr : ∃ m₁ : Γ(M, X.basicOpen (b * a i)), secs t _ m₁ =
          algebraMap Γ(X, V₀) Γ(X, X.basicOpen (b * a i)) c₀ :=
        ⟨M.presheaf.map (homOfLE hWb).op (algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) b ^ n • m'),
          by rw [secs_map, hm₀, algebraMap_basicOpen, algebraMap_basicOpen, res_res]⟩
      obtain ⟨g', hg'⟩ := ((hε i _ hW).1 _).1 hr
      have hua : IsUnit (algebraMap Γ(X, V₀) Γ(X, X.basicOpen (b * a i)) (a i)) :=
        isUnit_res_of_le_basicOpen (a i) _ hW
      have hεδ : X.presheaf.map (homOfLE hW).op (ε i) *
          algebraMap Γ(X, V₀) Γ(X, X.basicOpen (b * a i)) (a i) ^ m i =
          algebraMap Γ(X, V₀) Γ(X, X.basicOpen (b * a i)) (δ i) := by
        have e := congrArg (X.presheaf.map (homOfLE hW).op) (hδε i)
        rw [map_mul, map_pow, algebraMap_basicOpen, algebraMap_basicOpen, res_res, res_res] at e
        exact e
      have hmem : algebraMap Γ(X, V₀) Γ(X, X.basicOpen (b * a i)) c₀ ∈
          (Ideal.span {δ i}).map (algebraMap Γ(X, V₀) Γ(X, X.basicOpen (b * a i))) := by
        rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
        obtain ⟨U, hUe⟩ := hua.pow (m i)
        refine ⟨g' * ↑U⁻¹, ?_⟩
        rw [hg', ← hεδ, ← hUe, mul_comm g', mul_assoc]
        congr 1
        rw [mul_left_comm, Units.mul_inv, mul_one]
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Submonoid.powers (b * a i)) Γ(X, X.basicOpen (b * a i)) _ _).1 hmem
      exact ⟨k, hk⟩
    obtain ⟨N, hN⟩ := exists_pow_mem_sat T a δ b c₀ hsat
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (hgI _ hN)
    have hu := (hgb.mul (hbu.pow N)).mul (hbu.pow n)
    refine ⟨algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) q * ↑hu.unit⁻¹, ?_⟩
    have key : ↑hu.unit * secs t (X.basicOpen b) m' =
        algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) q * algebraMap Γ(X, V₀) Γ(X, X.basicOpen b) f := by
      conv_rhs => rw [← map_mul, hq, map_mul, map_mul, map_pow, ← hc₀]
      rw [IsUnit.unit_spec]
      ring
    calc secs t (X.basicOpen b) m'
        = ↑hu.unit⁻¹ * (↑hu.unit * secs t (X.basicOpen b) m') := by
          rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [key]; ring

end Factorial

/-- An ideal sheaf whose sections are those restricting into an invertible ideal on an open
subscheme is locally free of rank one, when the target is locally Noetherian and its
complementary local rings are factorial. -/
theorem isLocallyFreeRankOne_of_range_iff {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j]
    (hUFD : ∀ x : X, x ∉ Set.range j → UniqueFactorizationMonoid (X.presheaf.stalk x))
    (D : LineBundle Y) (s : D.obj ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono s]
    (M : X.Modules) (t : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono t]
    (ht : ∀ (W : X.Opens) (c : Γ(X, W)),
      (∃ m : Γ(M, W), t.app W m = c) ↔
        ∃ d : Γ(D.obj, j ⁻¹ᵁ W), s.app (j ⁻¹ᵁ W) d = j.app W c) :
    IsLocallyFreeRankOne M := by
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨O, hxO, σ, hσ⟩ := exists_isFrameOn_of_mem_range j s t D.property ht hx
    exact exists_restrict_iso_of_isFrameOn hσ hxO
  · obtain ⟨O, hxO, σ, hσ⟩ := exists_isFrameOn_of_factorial j s t D.property ht x (hUFD x hx)
    exact exists_restrict_iso_of_isFrameOn hσ hxO

end Complement

end Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal
