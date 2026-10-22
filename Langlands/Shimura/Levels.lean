import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Group.End

/-! # Double-quotient level spaces and their Hecke maps -/

universe u v w

namespace Langlands.Shimura

open CategoryTheory

/-- An actual compact open subgroup, used as a level. -/
structure CompactOpenLevel (G : Type v) [Group G] [TopologicalSpace G] where
  openSubgroup : OpenSubgroup G
  isCompact : IsCompact (openSubgroup : Set G)

namespace CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G]

abbrev subgroup (K : CompactOpenLevel G) : Subgroup G := K.openSubgroup.toSubgroup

/-- A right-translation arrow, with the precise conjugation condition needed
to descend from source level to target level. -/
@[ext] structure Arrow (K L : CompactOpenLevel G) where
  element : G
  respects (k : G) : k ∈ K.subgroup → element⁻¹ * k * element ∈ L.subgroup

instance : Category (CompactOpenLevel G) where
  Hom := Arrow
  id K := ⟨1, fun k hk => by simpa using hk⟩
  comp {K L M} f g :=
    ⟨f.element * g.element, fun k hk => by
      simpa [mul_assoc] using g.respects _ (f.respects k hk)⟩
  id_comp f := by ext; exact one_mul _
  comp_id f := by ext; exact mul_one _
  assoc f g h := by ext; exact mul_assoc _ _ _

@[simp] theorem id_element (K : CompactOpenLevel G) :
    (𝟙 K : Arrow K K).element = 1 := rfl

@[simp] theorem comp_element {K L M : CompactOpenLevel G} (f : K ⟶ L) (g : L ⟶ M) :
    (f ≫ g).element = f.element * g.element := rfl

/-- The usual forgetful level arrow for an inclusion of subgroups. -/
def inclusion {K L : CompactOpenLevel G} (h : K.subgroup ≤ L.subgroup) : K ⟶ L :=
  ⟨1, fun k hk => by simpa using h hk⟩

section Hecke

variable [IsTopologicalGroup G]

/-- The intermediate level `K ∩ g L g⁻¹` for the Hecke correspondence. -/
def heckeLevel (K L : CompactOpenLevel G) (g : G) : CompactOpenLevel G where
  openSubgroup := K.openSubgroup ⊓
    L.openSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom
      (by change Continuous (fun x : G => g⁻¹ * x * (g⁻¹)⁻¹); fun_prop)
  isCompact := K.isCompact.inter_right
    (L.openSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom
      (by change Continuous (fun x : G => g⁻¹ * x * (g⁻¹)⁻¹); fun_prop)).isClosed

/-- First leg of the Hecke correspondence, forgetting level. -/
def heckeLeft (K L : CompactOpenLevel G) (g : G) : heckeLevel K L g ⟶ K :=
  inclusion (fun _ hk => hk.1)

/-- Second leg of the Hecke correspondence, right translation by `g`. -/
def heckeRight (K L : CompactOpenLevel G) (g : G) : heckeLevel K L g ⟶ L :=
  ⟨g, fun _ hk => by simpa [MulAut.conj_apply] using hk.2⟩

end Hecke
end CompactOpenLevel

section DoubleQuotient

variable {Γ : Type u} {G : Type v} {X : Type w}
variable [Group Γ] [Group G] [MulAction Γ X]
variable (ι : Γ →* G)

/-- The actual relation defining `Γ \ (X × G) / K`. -/
def levelSetoid (K : Subgroup G) : Setoid (X × G) where
  r x y := ∃ γ : Γ, ∃ k : G, k ∈ K ∧
    y.1 = γ • x.1 ∧ y.2 = ι γ * x.2 * k
  iseqv := by
    constructor
    · intro x
      exact ⟨1, 1, K.one_mem, by simp⟩
    · rintro x y ⟨γ, k, hk, hy₁, hy₂⟩
      refine ⟨γ⁻¹, k⁻¹, K.inv_mem hk, ?_, ?_⟩
      · simp [hy₁]
      · simp [hy₂, mul_assoc]
    · rintro x y z ⟨γ, k, hk, hy₁, hy₂⟩ ⟨δ, l, hl, hz₁, hz₂⟩
      refine ⟨δ * γ, k * l, K.mul_mem hk hl, ?_, ?_⟩
      · simp [hz₁, hy₁, mul_smul]
      · simp [hz₂, hy₂, mul_assoc]

/-- The double-quotient level space, before any canonical-model theorem. -/
def LevelSpace (K : Subgroup G) : Type (max v w) :=
  Quotient (levelSetoid (X := X) ι K)

namespace LevelSpace

variable {ι}

/-- Send a domain/finite-group pair to its double-quotient class. -/
def mk (K : Subgroup G) (x : X × G) : LevelSpace (X := X) ι K :=
  Quotient.mk _ x

theorem mk_eq_mk (K : Subgroup G) (x y : X × G) :
    mk (ι := ι) K x = mk K y ↔ ∃ γ : Γ, ∃ k : G, k ∈ K ∧
      y.1 = γ • x.1 ∧ y.2 = ι γ * x.2 * k :=
  Quotient.eq

theorem translate_respects {K L : Subgroup G} (g : G)
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L)
    (x y : X × G) (hxy : levelSetoid ι K x y) :
    levelSetoid ι L (x.1, x.2 * g) (y.1, y.2 * g) := by
  obtain ⟨γ, k, hk, hy₁, hy₂⟩ := hxy
  exact ⟨γ, g⁻¹ * k * g, hg k hk, hy₁, by simp [hy₂, mul_assoc]⟩

/-- Genuine right translation on the quotient, with well-definedness proved. -/
def translate {K L : Subgroup G} (g : G)
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) :
    LevelSpace (X := X) ι K → LevelSpace (X := X) ι L :=
  Quotient.map (fun x => (x.1, x.2 * g)) (translate_respects g hg)

@[simp] theorem translate_mk {K L : Subgroup G} (g : G)
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) (x : X × G) :
    translate (ι := ι) g hg (mk K x) = mk L (x.1, x.2 * g) := rfl

@[simp] theorem translate_one (K : Subgroup G) (q : LevelSpace (X := X) ι K) :
    translate 1 (by intro k hk; simpa using hk) q = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    change mk K (x.1, x.2 * 1) = mk K x
    simp

theorem translate_comp {K L M : Subgroup G} (g h : G)
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L)
    (hh : ∀ l ∈ L, h⁻¹ * l * h ∈ M)
    (q : LevelSpace (X := X) ι K) :
    translate h hh (translate g hg q) =
      translate (g * h) (by intro k hk; simpa [mul_assoc] using hh _ (hg k hk)) q := by
  induction q using Quotient.inductionOn with
  | h x =>
    change mk M (x.1, (x.2 * g) * h) = mk M (x.1, x.2 * (g * h))
    rw [mul_assoc]

theorem translate_surjective {K L : Subgroup G} (g : G)
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) :
    Function.Surjective (translate (X := X) (ι := ι) g hg) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    refine ⟨mk K (x.1, x.2 * g⁻¹), ?_⟩
    change mk L (x.1, x.2 * g⁻¹ * g) = mk L x
    simp

section Topology

variable [TopologicalSpace X] [TopologicalSpace G]

instance (K : Subgroup G) : TopologicalSpace (LevelSpace (X := X) ι K) :=
  inferInstanceAs (TopologicalSpace (Quotient (levelSetoid (X := X) ι K)))

theorem continuous_mk (K : Subgroup G) :
    Continuous (mk (X := X) (ι := ι) K) :=
  continuous_quotient_mk'

theorem continuous_translate [ContinuousMul G] {K L : Subgroup G} (g : G)
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) :
    Continuous (translate (X := X) (ι := ι) g hg) :=
  (continuous_fst.prodMk (continuous_snd.mul_const g)).quotient_map' _

/-- All transporter arrows act by continuous maps on actual quotient spaces. -/
def tower [ContinuousMul G] : CompactOpenLevel G ⥤ TopCat.{max v w} where
  obj K := TopCat.of (LevelSpace (X := X) ι K.subgroup)
  map f := TopCat.ofHom ⟨translate f.element f.respects,
    continuous_translate f.element f.respects⟩
  map_id K := by ext q; exact translate_one K.subgroup q
  map_comp f g := by ext q; exact (translate_comp f.element g.element
    f.respects g.respects q).symm

end Topology
end LevelSpace
end DoubleQuotient

end Langlands.Shimura
