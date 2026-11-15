import Langlands.Representation.Classification.MoeglinWaldspurgerPointBlocks
import Langlands.Representation.Aubert.GradedInductionAssociativityProof
import Langlands.Representation.Category.Twist

/-!
# Isomorphisms and embeddings up to rank transport

`CastIso X Y` and `Embeds X Y` relate smooth representations of general linear groups of
provably equal ranks, absorbing the exact rank transports. Binary products are compatible
with both relations, and the binary product is associative for positive ranks.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Isomorphism up to an exact rank equality. -/
def CastIso {r s : ℕ}
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear s F.Carrier)) :
    Prop :=
  ∃ h : r = s, Nonempty (T.castRank h X ≅ Y)

/-- Embedding up to an exact rank equality. -/
def Embeds {r s : ℕ}
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear s F.Carrier)) :
    Prop :=
  letI := T.topology
  ∃ h : r = s, SmoothRep.IsSubrepresentation (T.castRank h X) Y

variable {T}

section Relations

variable {r s t : ℕ}
  {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
  {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear s F.Carrier)}
  {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear t F.Carrier)}

theorem castIso_of_iso {X Y : letI := T.topology;
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)} (e : X ≅ Y) : CastIso T X Y :=
  ⟨rfl, ⟨e⟩⟩

theorem CastIso.refl (X : letI := T.topology;
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) : CastIso T X X :=
  ⟨rfl, ⟨Iso.refl _⟩⟩

theorem CastIso.symm (h : CastIso T X Y) : CastIso T Y X := by
  obtain ⟨rfl, ⟨e⟩⟩ := h
  exact ⟨rfl, ⟨e.symm⟩⟩

theorem CastIso.trans (h₁ : CastIso T X Y) (h₂ : CastIso T Y Z) : CastIso T X Z := by
  obtain ⟨rfl, ⟨e₁⟩⟩ := h₁
  obtain ⟨rfl, ⟨e₂⟩⟩ := h₂
  exact ⟨rfl, ⟨e₁ ≪≫ e₂⟩⟩

theorem castIso_castRank (h : r = s) (X : letI := T.topology;
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    CastIso T X (T.castRank h X) :=
  ⟨h, ⟨Iso.refl _⟩⟩

theorem embeds_of_isSubrepresentation {X Y : letI := T.topology;
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
    (h : letI := T.topology; SmoothRep.IsSubrepresentation X Y) : Embeds T X Y :=
  ⟨rfl, h⟩

theorem CastIso.embeds (h : CastIso T X Y) : Embeds T X Y := by
  let := T.topology
  obtain ⟨rfl, ⟨e⟩⟩ := h
  exact ⟨rfl, isSubrepresentation_of_iso' e⟩

theorem Embeds.trans (h₁ : Embeds T X Y) (h₂ : Embeds T Y Z) : Embeds T X Z := by
  let := T.topology
  obtain ⟨rfl, f⟩ := h₁
  obtain ⟨rfl, g⟩ := h₂
  exact ⟨rfl, isSubrepresentation_trans f g⟩

theorem Embeds.castIso_right (h₁ : Embeds T X Y) (h₂ : CastIso T Y Z) : Embeds T X Z :=
  h₁.trans h₂.embeds

theorem Embeds.castIso_left (h₁ : CastIso T X Y) (h₂ : Embeds T Y Z) : Embeds T X Z :=
  h₁.embeds.trans h₂

/-- From an embedding up to rank transport to an embedding into a transported target. -/
theorem Embeds.isSubrepresentation_castRank (h : Embeds T X Y) (e : s = r) :
    letI := T.topology; SmoothRep.IsSubrepresentation X (T.castRank e Y) := by
  obtain ⟨rfl, f⟩ := h
  exact f

end Relations

/-! ### Binary products -/

theorem binary_castRank_obj {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor a' b').obj (T.castRank ha A, T.castRank hb B) =
      T.castRank (by rw [ha, hb]) ((T.binaryNormalizedProductFunctor a b).obj (A, B)) := by
  subst ha hb
  rfl

theorem CastIso.binary {a a' b b' : ℕ}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {A' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a' F.Carrier)}
    {B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    {B' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b' F.Carrier)}
    (h₁ : CastIso T A A') (h₂ : CastIso T B B') :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor a b).obj (A, B))
      ((T.binaryNormalizedProductFunctor a' b').obj (A', B')) := by
  let := T.topology
  obtain ⟨rfl, ⟨e₁⟩⟩ := h₁
  obtain ⟨rfl, ⟨e₂⟩⟩ := h₂
  exact ⟨rfl, ⟨(T.binaryNormalizedProductFunctor a b).mapIso (Iso.prod e₁ e₂)⟩⟩

theorem Embeds.binary {a a' b b' : ℕ}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {A' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a' F.Carrier)}
    {B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    {B' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b' F.Carrier)}
    (h₁ : Embeds T A A') (h₂ : Embeds T B B') :
    letI := T.topology
    Embeds T ((T.binaryNormalizedProductFunctor a b).obj (A, B))
      ((T.binaryNormalizedProductFunctor a' b').obj (A', B')) := by
  let := T.topology
  obtain ⟨rfl, ⟨f₁, hf₁⟩⟩ := h₁
  obtain ⟨rfl, ⟨f₂, hf₂⟩⟩ := h₂
  let g : (A, B) ⟶ (A', B') := (f₁, f₂)
  exact ⟨rfl, ⟨(T.binaryNormalizedProductFunctor a b).map g,
    T.binaryProductMap_injective g hf₁ hf₂⟩⟩

/-- **Associativity** for positive ranks. -/
theorem castIso_assoc {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (C : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor (a + b) c).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B), C))
      ((T.binaryNormalizedProductFunctor a (b + c)).obj
        (A, (T.binaryNormalizedProductFunctor b c).obj (B, C))) := by
  let := T.topology
  refine ⟨Nat.add_assoc a b c, ⟨SmoothRep.mkIso ?_⟩⟩
  have hR : ((((T.binaryNormalizedProductFunctor a (b + c)).obj
        (A, (T.binaryNormalizedProductFunctor b c).obj (B, C))).representation.comp
          (reindex (R := F.Carrier) (finCongr (Nat.add_assoc a b c))).toMonoidHom).comp
          (reindex (R := F.Carrier) (finCongr (Nat.add_assoc a b c))).symm.toMonoidHom) =
      ((T.binaryNormalizedProductFunctor a (b + c)).obj
        (A, (T.binaryNormalizedProductFunctor b c).obj (B, C))).representation := by
    ext g : 1
    simp
  exact Parabolic.equivTrans
    (Parabolic.equivSymm (T.castRankEquiv (Nat.add_assoc a b c) _))
    (Parabolic.equivTrans
      (Parabolic.equivPrecomp (Aubert.GradedAssociativityProof.binaryAssocEquiv F T ha hb hc A B C)
        (reindex (R := F.Carrier) (finCongr (Nat.add_assoc a b c))).symm.toMonoidHom)
      (equivOfRepresentationEq hR))

end Langlands.MoeglinWaldspurger.Derivation
