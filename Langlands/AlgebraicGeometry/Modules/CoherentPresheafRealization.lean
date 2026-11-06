import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Quasi-coherent module presheaves as actual module sheaves

A quasi-coherent `OModulePresheaf` `G` on a scheme `X` is realized as an actual sheaf of
modules: its sections over an open `O` are the families of sections of `G` over the affine
opens inside `O` that are compatible under restriction. On an affine open `U` these sections
are `G(U)`, naturally in `U`. When `X` is locally noetherian and `G` is coherent, the sheaf
is locally finitely presented.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.CoherentPresheafRealization

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (CommRingCat.of R)}

lemma presheaf_res_res {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

lemma presheaf_res_refl {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h).op).hom a = a := by
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, X.presheaf.map_id]
  rfl

lemma basicOpen_mul_le_left {U : X.Opens} (f g : Γ(X, U)) :
    X.basicOpen (f * g) ≤ X.basicOpen f := by
  rw [X.basicOpen_mul]
  exact inf_le_left

lemma basicOpen_mul_le_right {U : X.Opens} (f g : Γ(X, U)) :
    X.basicOpen (f * g) ≤ X.basicOpen g := by
  rw [X.basicOpen_mul]
  exact inf_le_right

section Local

variable {G : OModulePresheaf π}

/-- On an affine open, a section of a quasi-coherent presheaf that vanishes on the basic
opens of a family generating the unit ideal vanishes. -/
lemma eq_zero_of_res_basicOpen (hG : G.IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) (x : G.obj U)
    (hx : ∀ f ∈ s, G.res (X.basicOpen_le f) x = 0) : x = 0 := by
  have : x ∈ (⊥ : Submodule Γ(X, U) (G.obj U)) := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs x fun f => ?_
    obtain ⟨n, hn⟩ := (hG ⟨U, hU⟩ f.1).2 x (hx f.1 f.2)
    exact ⟨n, by simpa using hn⟩
  simpa using this

/-- On an affine open, compatible sections of a quasi-coherent presheaf over the basic opens
of a finite family generating the unit ideal glue. -/
lemma exists_res_eq_of_finset (hG : G.IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Finset Γ(X, U)) (hs : Ideal.span (s : Set Γ(X, U)) = ⊤)
    (t : ∀ f : Γ(X, U), G.obj (X.basicOpen f))
    (ht : ∀ f ∈ s, ∀ g ∈ s, G.res (basicOpen_mul_le_left f g) (t f) =
      G.res (basicOpen_mul_le_right f g) (t g)) :
    ∃ x : G.obj U, ∀ f ∈ s, G.res (X.basicOpen_le f) x = t f := by
  classical
  choose n y hy using fun f : Γ(X, U) => (hG ⟨U, hU⟩ f).1 (t f)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ f ∈ s, n f ≤ N := ⟨s.sup n, fun f hf => Finset.le_sup hf⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Γ(X, U) → G.obj U, ∀ f ∈ s, G.res (X.basicOpen_le f) (y' f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (f ^ N) • t f :=
    ⟨fun f => f ^ (N - n f) • y f, fun f hf => by
      dsimp only
      rw [G.res_smul, hy, smul_smul, ← map_mul, ← pow_add, Nat.sub_add_cancel (hN f hf)]⟩
  have key : ∀ f ∈ s, ∀ g ∈ s,
      G.res (X.basicOpen_le (f * g)) (g ^ N • y' f - f ^ N • y' g) = 0 := by
    intro f hf g hg
    have e1 : G.res (X.basicOpen_le (f * g)) (y' f) =
        (X.presheaf.map (homOfLE (X.basicOpen_le (f * g))).op).hom (f ^ N) •
          G.res (basicOpen_mul_le_left f g) (t f) := by
      rw [← G.res_res (basicOpen_mul_le_left f g) (X.basicOpen_le f), hy' f hf, G.res_smul,
        presheaf_res_res]
    have e2 : G.res (X.basicOpen_le (f * g)) (y' g) =
        (X.presheaf.map (homOfLE (X.basicOpen_le (f * g))).op).hom (g ^ N) •
          G.res (basicOpen_mul_le_right f g) (t g) := by
      rw [← G.res_res (basicOpen_mul_le_right f g) (X.basicOpen_le g), hy' g hg, G.res_smul,
        presheaf_res_res]
    rw [map_sub, G.res_smul, G.res_smul, e1, e2, ht f hf g hg, smul_smul, smul_smul, ← map_mul,
      ← map_mul, mul_comm (g ^ N), sub_self]
  have key' : ∀ f ∈ s, ∀ g ∈ s, ∃ m : ℕ, (f * g) ^ m • (g ^ N • y' f - f ^ N • y' g) = 0 :=
    fun f hf g hg => (hG ⟨U, hU⟩ (f * g)).2 _ (key f hf g hg)
  choose! m hm using key'
  obtain ⟨M, hM'⟩ : ∃ M : ℕ, ∀ f ∈ s, ∀ g ∈ s, m f g ≤ M :=
    ⟨s.sup fun f => s.sup (m f), fun f hf g hg =>
      (Finset.le_sup (f := m f) hg).trans (Finset.le_sup (f := fun f => s.sup (m f)) hf)⟩
  have hM : ∀ f ∈ s, ∀ g ∈ s, (f * g) ^ M • (g ^ N • y' f - f ^ N • y' g) = 0 := by
    intro f hf g hg
    rw [← Nat.sub_add_cancel (hM' f hf g hg), pow_add, mul_smul, hm f hf g hg, smul_zero]
  obtain ⟨w, hw⟩ : ∃ w : Γ(X, U) → G.obj U, ∀ f, w f = f ^ M • y' f := ⟨_, fun _ => rfl⟩
  have hz : ∀ f ∈ s, ∀ g ∈ s, g ^ (N + M) • w f = f ^ (N + M) • w g := by
    intro f hf g hg
    have h := hM f hf g hg
    rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at h
    rw [hw, hw, smul_smul, smul_smul]
    calc (g ^ (N + M) * f ^ M) • y' f = ((f * g) ^ M * g ^ N) • y' f := by
          congr 1; ring
      _ = ((f * g) ^ M * f ^ N) • y' g := h
      _ = (f ^ (N + M) * g ^ M) • y' g := by congr 1; ring
  have hsK := Ideal.span_pow_eq_top _ hs (N + M)
  rw [Set.image_eq_range] at hsK
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    ((Ideal.eq_top_iff_one _).mp hsK)
  simp only [smul_eq_mul] at hc
  let x : G.obj U := ∑ i : (s : Set Γ(X, U)), c i • w i.1
  have hx : ∀ f ∈ s, f ^ (N + M) • x = w f := by
    intro f hf
    simp only [x, Finset.smul_sum, smul_smul]
    calc ∑ i : (s : Set Γ(X, U)), (f ^ (N + M) * c i) • w i.1
        = ∑ i : (s : Set Γ(X, U)), (c i * i.1 ^ (N + M)) • w f := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_comm (f ^ (N + M)), mul_smul, hz i.1 (Finset.mem_coe.mp i.2) f hf, mul_smul]
      _ = (∑ i : (s : Set Γ(X, U)), c i * i.1 ^ (N + M)) • w f := by rw [Finset.sum_smul]
      _ = w f := by rw [hc, one_smul]
  refine ⟨x, fun f hf => ?_⟩
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (f ^ (N + M))) := by
    rw [map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen f).pow _
  rw [← hu.smul_left_cancel, ← G.res_smul, hx f hf, hw, G.res_smul, hy' f hf, smul_smul,
    ← map_mul, ← pow_add, add_comm M N]

/-- The sheaf property of a quasi-coherent presheaf on an affine open `V`, for a downward
closed family `P` of affine opens covering `V`. -/
theorem existsUnique_glue (hG : G.IsQuasicoherent) {V : X.Opens} (hV : IsAffineOpen V)
    (P : X.Opens → Prop) (hPa : ∀ W, P W → IsAffineOpen W)
    (hP : ∀ W W', IsAffineOpen W' → W' ≤ W → P W → P W')
    (hcov : ∀ x ∈ V, ∃ W, P W ∧ W ≤ V ∧ x ∈ W)
    (t : ∀ W, P W → G.obj W)
    (ht : ∀ W W' (h : W' ≤ W) (hW : P W) (hW' : P W'), G.res h (t W hW) = t W' hW') :
    ∃! x : G.obj V, ∀ W (hW : P W) (hWV : W ≤ V), G.res hWV x = t W hW := by
  classical
  let S : Set Γ(X, V) := {f | P (X.basicOpen f)}
  have hS : Ideal.span S = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨W, hW, hWV, hxW⟩ := hcov x hx
    obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le ⟨x, hxW⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨f, hP W _ (hV.basicOpen f) hfW hW⟩, hxf⟩
  have uniq : ∀ x₁ x₂ : G.obj V,
      (∀ f ∈ S, G.res (X.basicOpen_le f) x₁ = G.res (X.basicOpen_le f) x₂) → x₁ = x₂ := by
    intro x₁ x₂ h
    rw [← sub_eq_zero]
    exact eq_zero_of_res_basicOpen hG hV S hS _ fun f hf => by rw [map_sub, h f hf, sub_self]
  obtain ⟨s, hsS, hs⟩ := (Ideal.span_eq_top_iff_finite S).mp hS
  have hsP : ∀ f ∈ s, P (X.basicOpen f) := fun f hf => hsS (Finset.mem_coe.mpr hf)
  let t' : ∀ f : Γ(X, V), G.obj (X.basicOpen f) := fun f =>
    if h : P (X.basicOpen f) then t _ h else 0
  have ht' : ∀ f (hf : P (X.basicOpen f)), t' f = t _ hf := fun f hf => by simp [t', hf]
  obtain ⟨x, hx⟩ := exists_res_eq_of_finset hG hV s hs t' fun f hf g hg => by
    have hfg : P (X.basicOpen (f * g)) :=
      hP _ _ (hV.basicOpen _) (basicOpen_mul_le_left f g) (hsP f hf)
    rw [ht' f (hsP f hf), ht' g (hsP g hg), ht _ _ _ _ hfg, ht _ _ _ _ hfg]
  have hcovs : V ≤ ⨆ f : (s : Set Γ(X, V)), X.basicOpen f.1 :=
    hV.self_le_iSup_basicOpen_iff.mpr hs
  have hxW : ∀ W (hW : P W) (hWV : W ≤ V), G.res hWV x = t W hW := by
    intro W hW hWV
    have hWa := hPa W hW
    rw [← sub_eq_zero]
    let s' : Set Γ(X, W) := {g | ∃ f ∈ s, X.basicOpen g ≤ X.basicOpen f}
    have hs' : Ideal.span s' = ⊤ := by
      rw [← hWa.self_le_iSup_basicOpen_iff]
      intro y hy
      obtain ⟨⟨f, hf⟩, hyf⟩ := Opens.mem_iSup.mp (hcovs (hWV hy))
      obtain ⟨g, hgf, hyg⟩ := hWa.exists_basicOpen_le ⟨y, hyf⟩ hy
      exact Opens.mem_iSup.mpr ⟨⟨g, f, Finset.mem_coe.mp hf, hgf⟩, hyg⟩
    refine eq_zero_of_res_basicOpen hG hWa s' hs' _ fun g ⟨f, hf, hgf⟩ => ?_
    have hPg : P (X.basicOpen g) := hP W _ (hWa.basicOpen g) (X.basicOpen_le g) hW
    rw [map_sub, G.res_res, ht W _ _ hW hPg, ← G.res_res hgf (X.basicOpen_le f), hx f hf,
      ht' f (hsP f hf), ht _ _ _ _ hPg, sub_self]
  exact ⟨x, hxW, fun y hy => uniq _ _ fun f hf => (hy _ hf _).trans (hxW _ hf _).symm⟩

end Local

section Construction

/-- The affine opens contained in `O`. -/
abbrev AffBelow (O : X.Opens) : Type u := {V : X.Opens // IsAffineOpen V ∧ V ≤ O}

/-- Families of sections of `G` over the affine opens contained in `O`. -/
def Fam (G : OModulePresheaf π) (O : X.Opens) : Type u := ∀ V : AffBelow O, G.obj V.1

instance (G : OModulePresheaf π) (O : X.Opens) : AddCommGroup (Fam G O) :=
  inferInstanceAs (AddCommGroup (∀ V : AffBelow O, G.obj V.1))

instance (G : OModulePresheaf π) (O : X.Opens) : Module Γ(X, O) (Fam G O) where
  smul r s := fun V => (X.presheaf.map (homOfLE V.2.2).op).hom r • s V
  one_smul s := funext fun V => by
    change (X.presheaf.map (homOfLE V.2.2).op).hom 1 • s V = s V
    rw [map_one, one_smul]
  mul_smul r r' s := funext fun V => by
    change (X.presheaf.map (homOfLE V.2.2).op).hom (r * r') • s V =
      (X.presheaf.map (homOfLE V.2.2).op).hom r • (X.presheaf.map (homOfLE V.2.2).op).hom r' •
        s V
    rw [map_mul, mul_smul]
  smul_zero r := funext fun V => by
    change (X.presheaf.map (homOfLE V.2.2).op).hom r • (0 : G.obj V.1) = 0
    exact smul_zero _
  smul_add r s s' := funext fun V => by
    change (X.presheaf.map (homOfLE V.2.2).op).hom r • (s V + s' V) =
      (X.presheaf.map (homOfLE V.2.2).op).hom r • s V +
        (X.presheaf.map (homOfLE V.2.2).op).hom r • s' V
    exact smul_add _ _ _
  add_smul r r' s := funext fun V => by
    change (X.presheaf.map (homOfLE V.2.2).op).hom (r + r') • s V =
      (X.presheaf.map (homOfLE V.2.2).op).hom r • s V +
        (X.presheaf.map (homOfLE V.2.2).op).hom r' • s V
    rw [map_add, add_smul]
  zero_smul s := funext fun V => by
    change (X.presheaf.map (homOfLE V.2.2).op).hom 0 • s V = 0
    rw [map_zero, zero_smul]

/-- Families compatible under restriction between affine opens. -/
def compat (G : OModulePresheaf π) (O : X.Opens) : Submodule Γ(X, O) (Fam G O) where
  carrier := {s | ∀ (V W : AffBelow O) (h : W.1 ≤ V.1), G.res h (s V) = s W}
  add_mem' {a b} ha hb V W h := by
    change G.res h (a V + b V) = a W + b W
    rw [map_add, ha, hb]
  zero_mem' V W h := by
    change G.res h 0 = 0
    exact map_zero _
  smul_mem' r s hs V W h := by
    change G.res h ((X.presheaf.map (homOfLE V.2.2).op).hom r • s V) =
      (X.presheaf.map (homOfLE W.2.2).op).hom r • s W
    rw [G.res_smul, presheaf_res_res, hs]

/-- Restriction of compatible families. -/
def secRes (G : OModulePresheaf π) {O O' : X.Opens} (h : O' ≤ O) :
    compat G O →+ compat G O' where
  toFun s := ⟨fun V => s.1 ⟨V.1, V.2.1, V.2.2.trans h⟩, fun V W hWV =>
    s.2 ⟨V.1, V.2.1, V.2.2.trans h⟩ ⟨W.1, W.2.1, W.2.2.trans h⟩ hWV⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The abelian presheaf of compatible families. -/
def secPresheaf (G : OModulePresheaf π) : TopCat.Presheaf Ab.{u} X where
  obj O := AddCommGrpCat.of (compat G O.unop)
  map {O O'} i := AddCommGrpCat.ofHom (secRes G (leOfHom i.unop))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance (G : OModulePresheaf π) (O : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj O) ((secPresheaf G).obj O) :=
  inferInstanceAs (Module Γ(X, O.unop) (compat G O.unop))

/-- The presheaf of modules of compatible families. -/
def secModules (G : OModulePresheaf π) : PresheafOfModules.{u} X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (secPresheaf G) fun O O' i r s => by
    let s' : compat G O.unop := s
    apply Subtype.ext
    funext V
    change (X.presheaf.map (homOfLE (V.2.2.trans (leOfHom i.unop))).op).hom r •
        s'.1 ⟨V.1, V.2.1, V.2.2.trans (leOfHom i.unop)⟩ =
      (X.presheaf.map (homOfLE V.2.2).op).hom
        ((X.presheaf.map (homOfLE (leOfHom i.unop)).op).hom r) •
          s'.1 ⟨V.1, V.2.1, V.2.2.trans (leOfHom i.unop)⟩
    rw [presheaf_res_res]

variable {G : OModulePresheaf π}

/-- Compatible families glue, by the sheaf property of `G` on affine opens. -/
theorem secPresheaf_isSheaf (hG : G.IsQuasicoherent) : (secPresheaf G).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  apply TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types
  intro κ U sf hsf
  let sf' : ∀ k, compat G (U k) := sf
  have hcomp : ∀ k l V (hV : IsAffineOpen V) (hk : V ≤ U k) (hl : V ≤ U l),
      (sf' k).1 ⟨V, hV, hk⟩ = (sf' l).1 ⟨V, hV, hl⟩ := by
    intro k l V hV hk hl
    have h : secRes G (inf_le_left : U k ⊓ U l ≤ U k) (sf' k) =
        secRes G (inf_le_right : U k ⊓ U l ≤ U l) (sf' l) := hsf k l
    exact congrArg (fun z : compat G (U k ⊓ U l) => z.1 ⟨V, hV, le_inf hk hl⟩) h
  let P : X.Opens → Prop := fun W => IsAffineOpen W ∧ ∃ k, W ≤ U k
  let t : ∀ W, P W → G.obj W := fun W hW => (sf' hW.2.choose).1 ⟨W, hW.1, hW.2.choose_spec⟩
  have ht_eq : ∀ W (hW : P W) k (hk : W ≤ U k), t W hW = (sf' k).1 ⟨W, hW.1, hk⟩ :=
    fun W hW k hk => hcomp _ k W hW.1 hW.2.choose_spec hk
  have hglue : ∀ V : AffBelow (iSup U),
      ∃! x : G.obj V.1, ∀ W (hW : P W) (hWV : W ≤ V.1), G.res hWV x = t W hW := by
    intro V
    refine existsUnique_glue hG V.2.1 P (fun W hW => hW.1)
      (fun W W' hW' hle hW => ⟨hW', hW.2.choose, hle.trans hW.2.choose_spec⟩) ?_ t ?_
    · intro x hx
      obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (V.2.2 hx)
      obtain ⟨f, hfk, hxf⟩ := V.2.1.exists_basicOpen_le ⟨x, hk⟩ hx
      exact ⟨X.basicOpen f, ⟨V.2.1.basicOpen f, k, hfk⟩, X.basicOpen_le f, hxf⟩
    · intro W W' h hW hW'
      exact ((sf' _).2 ⟨W, hW.1, hW.2.choose_spec⟩ ⟨W', hW'.1, h.trans hW.2.choose_spec⟩ h).trans
        (ht_eq W' hW' _ (h.trans hW.2.choose_spec)).symm
  choose g hg hgu using hglue
  let s : compat G (iSup U) := ⟨fun V => g V, fun V W hWV =>
    hgu W _ fun W'' hW'' hW''W => by
      rw [G.res_res]
      exact hg V W'' hW'' (hW''W.trans hWV)⟩
  refine ⟨s, fun k => ?_, fun s' hs' => ?_⟩
  · change secRes G (le_iSup U k) s = sf' k
    apply Subtype.ext
    funext V
    refine (hgu ⟨V.1, V.2.1, V.2.2.trans (le_iSup U k)⟩ _ fun W hW hWV => ?_).symm
    exact ((sf' k).2 V ⟨W, hW.1, hWV.trans V.2.2⟩ hWV).trans (ht_eq W hW k (hWV.trans V.2.2)).symm
  · let s'' : compat G (iSup U) := s'
    change s'' = s
    have hs'' : ∀ k, secRes G (le_iSup U k) s'' = sf' k := hs'
    apply Subtype.ext
    funext V
    refine hgu V _ fun W hW hWV => ?_
    obtain ⟨k, hk⟩ := hW.2
    rw [s''.2 V ⟨W, hW.1, hWV.trans V.2.2⟩ hWV, ht_eq W hW k hk]
    exact congrArg (fun z : compat G (U k) => z.1 ⟨W, hW.1, hk⟩) (hs'' k)

variable (G) in
/-- The sheaf of modules of compatible families of sections of a quasi-coherent presheaf. -/
def realization (hG : G.IsQuasicoherent) : X.Modules where
  val := secModules G
  isSheaf := secPresheaf_isSheaf hG

/-- On an affine open, the sections of the realization are the sections of `G`. -/
def sectionsEquiv (hG : G.IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(realization G hG, U) ≃ₗ[Γ(X, U)] G.obj U where
  toFun s := (show compat G U from s).1 ⟨U, hU, le_rfl⟩
  invFun x := (⟨fun V => G.res V.2.2 x, fun V W h => G.res_res h V.2.2 x⟩ : compat G U)
  map_add' _ _ := rfl
  map_smul' r s := by
    change (X.presheaf.map (homOfLE le_rfl).op).hom r •
        (show compat G U from s).1 ⟨U, hU, le_rfl⟩ =
      r • (show compat G U from s).1 ⟨U, hU, le_rfl⟩
    rw [presheaf_res_refl]
  left_inv s := by
    apply Subtype.ext
    funext V
    exact (show compat G U from s).2 ⟨U, hU, le_rfl⟩ V V.2.2
  right_inv x := G.res_refl_apply U x

lemma sectionsEquiv_apply (hG : G.IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(realization G hG, U)) :
    sectionsEquiv hG hU s = (show compat G U from s).1 ⟨U, hU, le_rfl⟩ :=
  rfl

/-- The section identifications commute with restriction. -/
lemma sectionsEquiv_naturality (hG : G.IsQuasicoherent) {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : V ≤ U) (s : Γ(realization G hG, U)) :
    sectionsEquiv hG hV ((realization G hG).presheaf.map (homOfLE h).op s) =
      G.res h (sectionsEquiv hG hU s) :=
  ((show compat G U from s).2 ⟨U, hU, le_rfl⟩ ⟨V, hV, h⟩ h).symm

/-- The surjectivity half of quasi-coherence, for an open equal to a basic open. -/
lemma exists_res_eq_smul (hG : G.IsQuasicoherent) {W D : X.Opens} (hW : IsAffineOpen W)
    (g : Γ(X, W)) (hD : D = X.basicOpen g) (hle : D ≤ W) (x : G.obj D) :
    ∃ (n : ℕ) (y : G.obj W), G.res hle y = (X.presheaf.map (homOfLE hle).op).hom (g ^ n) • x := by
  subst hD
  exact (hG ⟨W, hW⟩ g).1 x

/-- The injectivity half of quasi-coherence, for an open equal to a basic open. -/
lemma exists_pow_smul_eq_zero (hG : G.IsQuasicoherent) {W D : X.Opens} (hW : IsAffineOpen W)
    (g : Γ(X, W)) (hD : D = X.basicOpen g) (hle : D ≤ W) (y : G.obj W)
    (hy : G.res hle y = 0) : ∃ n : ℕ, g ^ n • y = 0 := by
  subst hD
  exact (hG ⟨W, hW⟩ g).2 y hy

end Construction

section Chart

variable {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]

/-- The functions on the image of a spectrum chart given by the coordinate ring. -/
def chartHom : A →+* Γ(X, j ''ᵁ ⊤) := ((Scheme.ΓSpecIso A).inv ≫ (j.appIso ⊤).inv).hom

/-- The image of a basic open of a spectrum chart is a basic open. -/
lemma image_basicOpen_chart (f : A) :
    j ''ᵁ (PrimeSpectrum.basicOpen f : (Spec A).Opens) = X.basicOpen (chartHom j f) := by
  rw [← basicOpen_eq_of_affine, Scheme.image_basicOpen]
  rfl

/-- On a spectrum chart, the coordinate-ring action on the sections of a restriction is the
action of the corresponding functions on the image. -/
lemma smul_restrict_chart (M : X.Modules) {V : (Spec A).Opens} (a : A)
    (m : Γ(M.restrict j, V)) :
    a • m = (show Γ(M, j ''ᵁ V) from
      (X.presheaf.map (homOfLE (j.image_mono (le_top : V ≤ ⊤))).op).hom (chartHom j a) •
        (show Γ(M, j ''ᵁ V) from m)) := by
  rw [Scheme.Modules.smul_Spec_def]
  change (show Γ(M, j ''ᵁ V) from (j.appIso V).inv ((Spec A).presheaf.map V.leTop.op
      ((Scheme.ΓSpecIso A).inv a)) • (show Γ(M, j ''ᵁ V) from m)) = _
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_naturality]
  rfl

variable {G : OModulePresheaf π}

/-- On a spectrum chart with affine image, the restriction of the realization is
localizing: its sections over basic opens are localizations of its global sections. -/
theorem isLocalizing_restrict (hG : G.IsQuasicoherent) (hW : IsAffineOpen (j ''ᵁ ⊤)) :
    IsLocalizing (modulesSpecToSheaf.obj ((realization G hG).restrict j)) := by
  intro f
  have hDf : j ''ᵁ (PrimeSpectrum.basicOpen f : (Spec A).Opens) = X.basicOpen (chartHom j f) :=
    image_basicOpen_chart j f
  have hD : IsAffineOpen (j ''ᵁ (PrimeSpectrum.basicOpen f : (Spec A).Opens)) := by
    rw [hDf]
    exact hW.basicOpen _
  have hle : j ''ᵁ (PrimeSpectrum.basicOpen f : (Spec A).Opens) ≤ j ''ᵁ ⊤ := j.image_mono le_top
  have hres : ∀ x : Γ(realization G hG, j ''ᵁ ⊤),
      sectionsEquiv hG hD (((modulesSpecToSheaf.obj ((realization G hG).restrict j)).obj.map
        (PrimeSpectrum.basicOpen f).leTop.op).hom x) = G.res hle (sectionsEquiv hG hW x) :=
    fun x => sectionsEquiv_naturality hG hW hD hle x
  have hsmulD : ∀ (a : A)
      (y : Γ((realization G hG).restrict j, (PrimeSpectrum.basicOpen f : (Spec A).Opens))),
      sectionsEquiv hG hD (a • y) =
        (X.presheaf.map (homOfLE hle).op).hom (chartHom j a) • sectionsEquiv hG hD y := by
    intro a y
    rw [smul_restrict_chart j _ a y]
    exact (sectionsEquiv hG hD).map_smul _ _
  have hsmulW : ∀ (a : A) (x : Γ((realization G hG).restrict j, ⊤)),
      sectionsEquiv hG hW (a • x) = chartHom j a • sectionsEquiv hG hW x := by
    intro a x
    rw [smul_restrict_chart j _ a x, (sectionsEquiv hG hW).map_smul, presheaf_res_refl]
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro y
    obtain ⟨n, z, hz⟩ := exists_res_eq_smul hG hW (chartHom j f) hDf hle (sectionsEquiv hG hD y)
    refine ⟨n, (sectionsEquiv hG hW).symm z, (sectionsEquiv hG hD).injective ?_⟩
    rw [hsmulD, hres, LinearEquiv.apply_symm_apply, hz, map_pow]
  · intro x hx
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero hG hW (chartHom j f) hDf hle
      (sectionsEquiv hG hW x) (by rw [← hres, hx, map_zero])
    refine ⟨n, (sectionsEquiv hG hW).injective ?_⟩
    rw [hsmulW, map_pow, hn, map_zero]

/-- On a spectrum chart with affine image, the global sections of the restriction of the
realization of a presheaf with finite sections there are a finite module. -/
theorem finite_restrict (hG : G.IsQuasicoherent) (hW : IsAffineOpen (j ''ᵁ ⊤))
    [Module.Finite Γ(X, j ''ᵁ ⊤) (G.obj (j ''ᵁ ⊤))] :
    Module.Finite A (moduleSpecΓFunctor.obj ((realization G hG).restrict j)) := by
  let σ : Γ(X, j ''ᵁ ⊤) →+* A := ((j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso A).hom).hom
  let e : G.obj (j ''ᵁ ⊤) →ₛₗ[σ] moduleSpecΓFunctor.obj ((realization G hG).restrict j) :=
    { toFun := (sectionsEquiv hG hW).symm
      map_add' := map_add _
      map_smul' := fun r x => by
        rw [(sectionsEquiv hG hW).symm.map_smul]
        exact (restrict_smul_Spec j (realization G hG) r ((sectionsEquiv hG hW).symm x)).symm }
  exact Module.Finite.of_surjective e (sectionsEquiv hG hW).symm.surjective

end Chart

variable {G : OModulePresheaf π}

/-- The realization of a coherent quasi-coherent presheaf on a locally noetherian scheme is
locally finitely presented. -/
theorem isFinitePresentation_realization [IsLocallyNoetherian X] (hG : G.IsQuasicoherent)
    (hG' : G.IsCoherent) : (realization G hG).IsFinitePresentation := by
  refine isFinitePresentation_of_forall_exists_presentation _ fun y => ?_
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have hW : IsAffineOpen (hU.fromSpec ''ᵁ ⊤) :=
    (isAffineOpen_top (Spec Γ(X, U))).image_of_isOpenImmersion hU.fromSpec
  have : Module.Finite Γ(X, hU.fromSpec ''ᵁ ⊤) (G.obj (hU.fromSpec ''ᵁ ⊤)) := hG' ⟨_, hW⟩
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := finite_restrict hU.fromSpec hG hW
  have := Module.finitePresentation_of_finite Γ(X, U)
    (moduleSpecΓFunctor.obj ((realization G hG).restrict hU.fromSpec))
  obtain ⟨P, hP⟩ := exists_presentation_tilde
    (moduleSpecΓFunctor.obj ((realization G hG).restrict hU.fromSpec))
  have : IsIso ((realization G hG).restrict hU.fromSpec).fromTildeΓ :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mpr (isLocalizing_restrict hU.fromSpec hG hW)
  obtain ⟨P', hP'⟩ := exists_presentation_opensRange (realization G hG) hU.fromSpec
    (P.ofIsIso ((realization G hG).restrict hU.fromSpec).fromTildeΓ)
  refine ⟨hU.fromSpec.opensRange, ?_, P', hP'⟩
  rw [hU.opensRange_fromSpec]
  exact hyU

/-- A coherent quasi-coherent presheaf on a locally noetherian scheme is the restriction to
affine opens of a locally finitely presented sheaf of modules. -/
theorem exists_modules_sectionsEquiv [IsLocallyNoetherian X] (hG : G.IsQuasicoherent)
    (hG' : G.IsCoherent) :
    ∃ (M : X.Modules) (e : ∀ U : X.affineOpens, Γ(M, U.1) ≃ₗ[Γ(X, U.1)] G.obj U.1),
      M.IsFinitePresentation ∧ ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (s : Γ(M, U.1)),
        e V (M.presheaf.map (homOfLE h).op s) = G.res h (e U s) :=
  ⟨realization G hG, fun U => sectionsEquiv hG U.2, isFinitePresentation_realization hG hG',
    fun U V h s => sectionsEquiv_naturality hG U.2 V.2 h s⟩

end Langlands.AlgebraicGeometry.Modules.CoherentPresheafRealization
