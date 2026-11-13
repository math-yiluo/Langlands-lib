import Langlands.Sheaf.Renard.CompactOpenSheafCharacterizationStatements
import Langlands.Sheaf.Renard.SheafGermUnitIsoProof

/-! # Compact-open sections as increasing subgroups of global germ sections -/

set_option autoImplicit false

noncomputable section

open TopologicalSpace

namespace Langlands.Sheaf.Renard

universe u v

namespace CompactOpenSheafCharacterization

open ProjectorBasisSheaf

variable {X : Type u} [TopologicalSpace X]
variable (hX : Langlands.Topology.IsLocallyProfinite X)
variable (F : BasisSheaf.{u,v} (compactOpenBasis hX))

/-- Global locally represented germ sections which vanish outside a compact open. -/
def boundedSubgroup : AddSubgroup (GermSections F.obj.obj (⊤ : Opens X)) where
  carrier := {s | ∃ U : CompactOpen hX, ∀ x : X, x ∉ U.obj → s.val ⟨x, trivial⟩ = 0}
  zero_mem' := ⟨emptyOpen hX, fun _ _ => rfl⟩
  add_mem' := by
    rintro s t ⟨U, hs⟩ ⟨V, ht⟩
    refine ⟨unionOpen hX U V, ?_⟩
    intro x hx
    change s.val ⟨x, trivial⟩ + t.val ⟨x, trivial⟩ = 0
    rw [hs x (fun h => hx (Or.inl h)), ht x (fun h => hx (Or.inr h)), add_zero]
  neg_mem' := by
    rintro s ⟨U, hs⟩
    refine ⟨U, ?_⟩
    intro x hx
    change -s.val ⟨x, trivial⟩ = 0
    rw [hs x hx, neg_zero]

/-- The common abelian group, in the joint space and value universe. -/
abbrev Carrier : Type (max u v) := ↥(boundedSubgroup hX F)

/-- The subgroup of global sections vanishing off the given compact open. -/
def supported (U : CompactOpen hX) : AddSubgroup (Carrier hX F) where
  carrier := {s | ∀ x : X, x ∉ U.obj → s.val.val ⟨x, trivial⟩ = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro s t hs ht x hx
    change s.val.val ⟨x, trivial⟩ + t.val.val ⟨x, trivial⟩ = 0
    rw [hs x hx, ht x hx, add_zero]
  neg_mem' := by
    intro s hs x hx
    change -s.val.val ⟨x, trivial⟩ = 0
    rw [hs x hx, neg_zero]

open Classical in
/-- The germ family of an original section, extended by zero. -/
def extensionFamily (U : CompactOpen hX) (s : Sections F.obj.obj U) :
    GermFamily F.obj.obj (⊤ : Opens X) :=
  fun x => if hx : x.val ∈ U.obj then rawGerm F.obj.obj U x.val hx s else 0

theorem extensionFamily_mem (U : CompactOpen hX) (s : Sections F.obj.obj U)
    (x : X) (hx : x ∈ U.obj) :
    extensionFamily hX F U s ⟨x, trivial⟩ = rawGerm F.obj.obj U x hx s := by
  classical
  exact dite_eq_left hx

theorem extensionFamily_not_mem (U : CompactOpen hX) (s : Sections F.obj.obj U)
    (x : X) (hx : x ∉ U.obj) :
    extensionFamily hX F U s ⟨x, trivial⟩ = 0 := by
  classical
  exact dite_eq_right hx

/-- The clopen complement supplies zero local representatives outside the original open. -/
theorem extensionFamily_locallyRepresented (U : CompactOpen hX)
    (s : Sections F.obj.obj U) :
    LocallyRepresented F.obj.obj ⊤ (extensionFamily hX F U s) := by
  intro x
  by_cases hx : x.val ∈ U.obj
  · exact ⟨U, hx, le_top, s, fun y hy => (extensionFamily_mem hX F U s y hy).symm⟩
  · let C : Opens X := ⟨(U.obj : Set X)ᶜ, (clopen hX U).isClosed.isOpen_compl⟩
    obtain ⟨V, hxV, hVC⟩ := (compactOpenBasis hX).exists_subset C hx
    refine ⟨V, hxV, le_top, 0, ?_⟩
    intro y hy
    rw [rawGerm_zero, extensionFamily_not_mem hX F U s y (hVC hy)]

/-- The extended section is a member of the supported subgroup. -/
def extend (U : CompactOpen hX) (s : Sections F.obj.obj U) : supported hX F U :=
  ⟨⟨⟨extensionFamily hX F U s, extensionFamily_locallyRepresented hX F U s⟩,
    U, extensionFamily_not_mem hX F U s⟩, extensionFamily_not_mem hX F U s⟩

/-- Extension by zero respects addition. -/
def extendHom (U : CompactOpen hX) : Sections F.obj.obj U →+ supported hX F U where
  toFun := extend hX F U
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    apply GermSections.ext
    intro x
    change extensionFamily hX F U 0 x = 0
    by_cases hx : x.val ∈ U.obj
    · rw [extensionFamily_mem hX F U 0 x.val hx, rawGerm_zero]
    · exact extensionFamily_not_mem hX F U 0 x.val hx
  map_add' s t := by
    apply Subtype.ext
    apply Subtype.ext
    apply GermSections.ext
    intro x
    change extensionFamily hX F U (s + t) x =
      extensionFamily hX F U s x + extensionFamily hX F U t x
    by_cases hx : x.val ∈ U.obj
    · rw [extensionFamily_mem hX F U _ x.val hx,
        extensionFamily_mem hX F U _ x.val hx,
        extensionFamily_mem hX F U _ x.val hx, map_add]
    · rw [extensionFamily_not_mem hX F U _ x.val hx,
        extensionFamily_not_mem hX F U _ x.val hx,
        extensionFamily_not_mem hX F U _ x.val hx, add_zero]

/-- Sheaf descent identifies supported global germ sections with original sections. -/
theorem extendHom_bijective (U : CompactOpen hX) :
    Function.Bijective (extendHom hX F U) := by
  constructor
  · intro s t h
    apply (sheafSectionGermsBijective F U).1
    apply GermSections.ext
    intro x
    simp only [sectionGerms_apply]
    have he := congrArg (fun z : supported hX F U => z.val.val.val ⟨x.val, trivial⟩) h
    change extensionFamily hX F U s ⟨x.val, trivial⟩ =
      extensionFamily hX F U t ⟨x.val, trivial⟩ at he
    simpa only [extensionFamily_mem hX F U _ x.val x.property] using he
  · intro y
    obtain ⟨s, hs⟩ := (sheafSectionGermsBijective F U).2
      (germRestriction F.obj.obj (show U.obj ≤ ⊤ from le_top) y.val.val)
    refine ⟨s, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply GermSections.ext
    intro x
    change extensionFamily hX F U s x = y.val.val.val x
    by_cases hx : x.val ∈ U.obj
    · rw [extensionFamily_mem hX F U s x.val hx]
      exact congrArg (fun z : GermSections F.obj.obj U.obj => z.val ⟨x.val, hx⟩) hs
    · rw [extensionFamily_not_mem hX F U s x.val hx]
      exact (y.property x.val hx).symm

/-- The required additive identification is the actual extension-by-zero map. -/
def equiv (U : CompactOpen hX) : Sections F.obj.obj U ≃+ supported hX F U :=
  AddEquiv.ofBijective (extendHom hX F U) (extendHom_bijective hX F U)

theorem equiv_mem (U : CompactOpen hX) (s : Sections F.obj.obj U)
    (x : X) (hx : x ∈ U.obj) :
    (equiv hX F U s).val.val.val ⟨x, trivial⟩ = rawGerm F.obj.obj U x hx s :=
  extensionFamily_mem hX F U s x hx

theorem equiv_symm_germ (U : CompactOpen hX) (y : supported hX F U)
    (x : X) (hx : x ∈ U.obj) :
    rawGerm F.obj.obj U x hx ((equiv hX F U).symm y) =
      y.val.val.val ⟨x, trivial⟩ := by
  rw [← equiv_mem hX F U _ x hx, (equiv hX F U).apply_symm_apply]

end CompactOpenSheafCharacterization

/-- Renard II.2.4, Proposition, with both original universes unchanged. -/
theorem compactOpenSheafCharacterization :
    CompactOpenSheafCharacterizationStatement.{u,v} := by
  intro X _ hX F
  let Fc := CompactOpenSheafCharacterization.Carrier hX F
  let S := CompactOpenSheafCharacterization.supported hX F
  let φ := CompactOpenSheafCharacterization.equiv hX F
  refine ⟨Fc, inferInstance, S, φ, ?_, ?_, ?_, ?_⟩
  · intro U V h y hy x hx
    exact hy x (fun hU => hx (h hU))
  · intro y
    exact y.property
  · intro U V hUV y hyU hyV
    apply Subtype.ext
    apply GermSections.ext
    intro x
    by_cases hx : x.val ∈ U.obj
    · change (CompactOpenSheafCharacterization.equiv hX F U _).val.val.val x =
        y.val.val x
      rw [CompactOpenSheafCharacterization.equiv_mem hX F U _ x.val hx,
        rawGerm_restriction,
        CompactOpenSheafCharacterization.equiv_symm_germ hX F V _ x.val (hUV hx)]
    · change (CompactOpenSheafCharacterization.equiv hX F U _).val.val.val x =
        y.val.val x
      rw [(φ U _).property x.val hx, hyU x.val hx]
  · intro U V W hWV _ hW y hyU hyV
    apply (sheafSectionGermsBijective F W).1
    apply GermSections.ext
    intro x
    simp only [sectionGerms_apply, rawGerm_zero]
    rw [rawGerm_restriction,
      CompactOpenSheafCharacterization.equiv_symm_germ hX F V _ x.val (hWV x.property)]
    have hxW : x.val ∈ (W.obj : Set X) := x.property
    rw [hW] at hxW
    exact hyU x.val hxW.2

end Langlands.Sheaf.Renard
