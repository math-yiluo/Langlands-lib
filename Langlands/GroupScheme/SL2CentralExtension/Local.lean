import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Fppf-local properties of test morphisms over a scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

/-- A property of morphisms `g : V ⟶ T` in `Over S` holds fppf-locally on `T` if it holds on
every member of some covering sieve of `T` for the fppf topology on `Over S`. -/
def Loc {T : Over S} (P : ∀ ⦃V : Over S⦄, (V ⟶ T) → Prop) : Prop :=
  ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧ ∀ ⦃V : Over S⦄ (g : V ⟶ T), R g → P g

namespace Loc

variable {T : Over S} {P Q : ∀ ⦃V : Over S⦄, (V ⟶ T) → Prop}

theorem of_forall (h : ∀ ⦃V : Over S⦄ (g : V ⟶ T), P g) : Loc P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ g _ => h g⟩

theorem mono (h : Loc P) (hPQ : ∀ ⦃V : Over S⦄ (g : V ⟶ T), P g → Q g) : Loc Q := by
  obtain ⟨R, hR, hP⟩ := h
  exact ⟨R, hR, fun _ g hg => hPQ g (hP g hg)⟩

theorem and (hP : Loc P) (hQ : Loc Q) : Loc (fun _ g => P g ∧ Q g) := by
  obtain ⟨R, hR, hP⟩ := hP
  obtain ⟨R', hR', hQ⟩ := hQ
  exact ⟨R ⊓ R', GrothendieckTopology.intersection_covering _ hR hR',
    fun _ g hg => ⟨hP g hg.1, hQ g hg.2⟩⟩

theorem pull (h : Loc P) {T' : Over S} (f : T' ⟶ T) :
    Loc (fun _ (g : _ ⟶ T') => P (g ≫ f)) := by
  obtain ⟨R, hR, hP⟩ := h
  exact ⟨R.pullback f, GrothendieckTopology.pullback_stable _ f hR, fun _ g hg => hP _ hg⟩

theorem bind (h : Loc P) (hPQ : ∀ ⦃V : Over S⦄ (g : V ⟶ T), P g →
    Loc (fun _ (k : _ ⟶ V) => Q (k ≫ g))) : Loc Q := by
  obtain ⟨R, hR, hP⟩ := h
  choose R' hR' hQ using fun V (g : V ⟶ T) (hg : R g) => hPQ g (hP g hg)
  refine ⟨Sieve.bind R.arrows (fun V g hg => R' V g hg),
    GrothendieckTopology.bind_covering _ hR (fun V g hg => hR' V g hg), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g hg k hk

/-- Fppf-local equality of two morphisms implies equality: representable presheaves are
fppf sheaves. -/
theorem ext {X : Over S} {x y : T ⟶ X} (h : Loc (fun _ g => g ≫ x = g ≫ y)) : x = y := by
  obtain ⟨R, hR, hxy⟩ := h
  have hs : Presieve.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj X) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  exact (hs.isSeparated R hR).ext (fun _ g hg => hxy g hg)

/-- Gluing of morphisms characterized by a restriction-stable property with unique
solutions, which exist fppf-locally. -/
theorem glue {X : Over S} (P : ∀ ⦃V : Over S⦄, (V ⟶ T) → (V ⟶ X) → Prop)
    (hstab : ∀ ⦃V W : Over S⦄ (g : V ⟶ T) (k : W ⟶ V) (x : V ⟶ X), P g x → P (k ≫ g) (k ≫ x))
    (huniq : ∀ ⦃V : Over S⦄ (g : V ⟶ T) (x y : V ⟶ X), P g x → P g y → x = y)
    (hloc : Loc (fun _ g => ∃ x, P g x)) :
    ∃ e : T ⟶ X, ∀ ⦃V : Over S⦄ (g : V ⟶ T) (x : V ⟶ X), P g x → g ≫ e = x := by
  obtain ⟨R, hR, hex⟩ := hloc
  choose x hx using hex
  have hs : Presieve.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj X) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let fam : Presieve.FamilyOfElements (yoneda.obj X) R.arrows := fun V g hg => x g hg
  have hc : fam.Compatible := by
    intro Y₁ Y₂ W f₁ f₂ g₁ g₂ h₁ h₂ w
    change f₁ ≫ x g₁ h₁ = f₂ ≫ x g₂ h₂
    have e₁ := hstab g₁ f₁ _ (hx g₁ h₁)
    have e₂ := hstab g₂ f₂ _ (hx g₂ h₂)
    rw [w] at e₁
    exact huniq _ _ _ e₁ e₂
  refine ⟨(hs R hR).amalgamate fam hc, fun V g y hy => ?_⟩
  apply ext
  refine ⟨R.pullback g, GrothendieckTopology.pullback_stable _ g hR, fun W k hk => ?_⟩
  have h1 : (k ≫ g) ≫ (hs R hR).amalgamate fam hc = x (k ≫ g) hk :=
    (hs R hR).valid_glue hc (k ≫ g) hk
  change k ≫ g ≫ (hs R hR).amalgamate fam hc = k ≫ y
  rw [← Category.assoc, h1]
  exact huniq _ _ _ (hx _ hk) (hstab g k y hy)

/-- A covering presieve of `T.left` for the fppf precoverage gives an fppf-local property. -/
theorem of_presieve {R : Presieve T.left} (hR : R ∈ Scheme.fppfPrecoverage T.left) :
    Loc (fun V (g : V ⟶ T) => ∃ (W : Scheme.{u}) (k : V.left ⟶ W) (f : W ⟶ T.left),
      R f ∧ k ≫ f = g.left) := by
  refine ⟨(Sieve.overEquiv T).symm (Sieve.generate R),
    GrothendieckTopology.overEquiv_symm_mem_over _ _ _
      (Precoverage.generate_mem_toGrothendieck hR), fun V g hg => ?_⟩
  rw [Sieve.overEquiv_symm_iff] at hg
  obtain ⟨W, k, f, hf, hkf⟩ := hg
  exact ⟨W, k, f, hf, hkf⟩

/-- The members of an fppf cover of `T.left` form an fppf-local family. -/
theorem of_cover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left) :
    Loc (fun V (g : V ⟶ T) => ∃ (i : 𝒰.I₀) (k : V ⟶ Over.mk (𝒰.f i ≫ T.hom)),
      k ≫ (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) = g) := by
  refine (of_presieve (R := Presieve.ofArrows 𝒰.X 𝒰.f) 𝒰.mem₀).mono ?_
  rintro V g ⟨W, k, _, ⟨i⟩, hkf⟩
  refine ⟨i, Over.homMk k ?_, ?_⟩
  · change k ≫ 𝒰.f i ≫ T.hom = V.hom
    rw [← Category.assoc, hkf, Over.w]
  · ext
    exact hkf

/-- A single flat, surjective morphism locally of finite presentation is an fppf cover. -/
theorem of_single {T₀ : Over S} (f : T₀ ⟶ T) [Flat f.left] [Surjective f.left]
    [LocallyOfFinitePresentation f.left] :
    Loc (fun V (g : V ⟶ T) => ∃ k : V ⟶ T₀, k ≫ f = g) := by
  refine (of_presieve (R := Presieve.singleton f.left)
    (Scheme.Hom.singleton_mem_fppfPrecoverage f.left)).mono ?_
  rintro V g ⟨W, k, _, ⟨⟩, hkf⟩
  refine ⟨Over.homMk k ?_, ?_⟩
  · rw [← Over.w f, ← Category.assoc, hkf, Over.w]
  · ext
    exact hkf

/-- To prove a property fppf-locally, it suffices to do so over affine test schemes. -/
theorem of_affine (h : ∀ ⦃V : Over S⦄ (g : V ⟶ T), IsAffine V.left →
    Loc (fun _ (k : _ ⟶ V) => P (k ≫ g))) : Loc P := by
  let 𝒰 := T.left.affineCover
  refine (of_presieve (R := Presieve.ofArrows 𝒰.X 𝒰.f)
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ 𝒰.mem₀)).bind ?_
  rintro V g ⟨W, k, _, ⟨i⟩, hkf⟩
  let Vi : Over S := Over.mk (𝒰.f i ≫ T.hom)
  let ji : Vi ⟶ T := Over.homMk (𝒰.f i) rfl
  have hk : k ≫ 𝒰.f i ≫ T.hom = V.hom := by rw [← Category.assoc, hkf, Over.w]
  let k' : V ⟶ Vi := Over.homMk k hk
  have hg : g = k' ≫ ji := by ext; exact hkf.symm
  have : IsAffine Vi.left := inferInstanceAs (IsAffine (𝒰.X i))
  refine ((h ji this).pull k').mono ?_
  intro U m hm
  rw [hg, ← Category.assoc]
  exact hm

end Loc

end Langlands.GroupScheme.SL2CentralExtension
