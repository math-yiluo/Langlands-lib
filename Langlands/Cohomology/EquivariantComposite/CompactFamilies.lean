import Langlands.Cohomology.EquivariantComposite.CompactAction
import Langlands.Sheaf.Equivariant.CoinducedFamilies
import Langlands.Sheaf.Equivariant.SmoothCompactSupport
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Compact indexed families as smooth cofree representations -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Sheaf.Equivariant
open scoped Pointwise

namespace Langlands.Cohomology.EquivariantComposite

universe u

variable {R G X : Type u} [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]

/-- Ordinary presheaf of arbitrary entries in a point-indexed coefficient family. -/
def ordinaryFamilies (A : X → ModuleCat.{u} R) :
    (TopCat.of X).Presheaf (ModuleCat.{u} R) where
  obj U := ModuleCat.of R (∀ y : U.unop, A y.val)
  map f := ModuleCat.ofHom
    { toFun s y := s ⟨y.val, f.unop.le y.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Vanishing of a global germ is witnessed by a zero restriction. -/
theorem ordinary_germ_zero_iff (F : (TopCat.of X).Presheaf (ModuleCat.{u} R))
    (s : F.obj (op ⊤)) (x : X) :
    F.Γgerm x s = 0 ↔ ∃ (U : Opens X) (_ : x ∈ U),
      F.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0 := by
  constructor
  · intro hx
    obtain ⟨U, hxU, i, j, hU⟩ := F.germ_eq x (U := ⊤) (V := ⊤)
      trivial trivial s 0 (by simpa [TopCat.Presheaf.Γgerm] using hx)
    have hi : i = homOfLE (show U ≤ ⊤ from le_top) := Subsingleton.elim _ _
    rw [hi] at hU
    exact ⟨U, hxU, by simpa only [map_zero] using hU⟩
  · rintro ⟨U, hxU, hU⟩
    rw [← F.Γgerm_res_apply x hxU s (i := homOfLE (show U ≤ ⊤ from le_top)), hU]
    exact map_zero _

/-- A zero germ of an arbitrary family forces its entry at that point to vanish. -/
theorem ordinaryFamilies_value_zero (A : X → ModuleCat.{u} R)
    (s : (ordinaryFamilies A).obj (op ⊤)) (x : X)
    (hx : (ordinaryFamilies A).Γgerm x s = 0) : s ⟨x, trivial⟩ = 0 := by
  obtain ⟨U, hxU, hU⟩ := (ordinary_germ_zero_iff (ordinaryFamilies A) s x).1 hx
  exact congrFun hU ⟨x, hxU⟩

/-- A row of a global indexed family. -/
def familyRow (A : X → ModuleCat.{u} R)
    (s : (CoinducedFamilies.presheaf (G := G) A).obj (op ActionOpens.top)) (g : G) :
    (ordinaryFamilies A).obj (op ⊤) := fun y => s g ⟨y.val, trivial⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousConstSMul G X]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Each row's support lies in the inverse translate of the indexed support. -/
theorem support_familyRow_subset (A : X → ModuleCat.{u} R)
    (s : (CoinducedFamilies.presheaf (G := G) A).obj (op ActionOpens.top)) (g : G) :
    Langlands.Sheaf.CompactSupport.support (ordinaryFamilies A) (familyRow A s g) ⊆
      (fun x : X => g⁻¹ • x) '' Langlands.Sheaf.CompactSupport.support
        (CompactSections.ordinary (CoinducedFamilies.presheaf A)) s := by
  intro y hy
  refine ⟨g • y, ?_, inv_smul_smul g y⟩
  intro hz
  apply hy
  obtain ⟨U, hyU, hU⟩ := (CompactSections.germ_zero_iff
    (CoinducedFamilies.presheaf A) s (g • y)).1 hz
  apply (ordinary_germ_zero_iff (ordinaryFamilies A) (familyRow A s g) y).2
  refine ⟨CoinducedFamilies.coordinateOpen U g, hyU, ?_⟩
  funext z
  have h := congrFun (congrFun hU g) ⟨z.val, z.property⟩
  change s ((1 : G) * g) ⟨z.val, _⟩ = 0 at h
  change s g ⟨z.val, trivial⟩ = 0
  exact (CoinducedFamilies.families_congr s (one_mul g) z.val _ _).symm.trans h

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Compactness of indexed support implies compactness of each row. -/
theorem isCompact_support_familyRow (A : X → ModuleCat.{u} R)
    (s : Langlands.Sheaf.CompactSupport.submodule
      (CompactSections.ordinary (CoinducedFamilies.presheaf (G := G) A))) (g : G) :
    IsCompact (Langlands.Sheaf.CompactSupport.support (ordinaryFamilies A)
      (familyRow A s.val g)) :=
  (s.property.image (continuous_const_smul g⁻¹)).of_isClosed_subset
    (Langlands.Sheaf.CompactSupport.isClosed_support _ _) (support_familyRow_subset A s.val g)

/-- Compact rows, using actual germ support in the ordinary family presheaf. -/
abbrev compactRows (A : X → ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (Langlands.Sheaf.CompactSupport.submodule (ordinaryFamilies A))

/-- Read an indexed compact section as a group function of compact rows. -/
def compactFamilyRows (A : X → ModuleCat.{u} R) :
    (CompactSections.representation (CoinducedFamilies.presheaf A)).IntertwiningMap
      (functionRepresentation R G (compactRows A)) where
  toLinearMap :=
    { toFun s g := ⟨familyRow A s.val g, isCompact_support_familyRow A s g⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

/-- Saturation of a closed set is closed when the acting group is compact. -/
theorem isClosed_compactSaturation [CompactSpace G] [HasStableNeighbourhoods G X]
    {K : Set X} (hK : IsClosed K) : IsClosed (compactSaturation (G := G) K) := by
  let : ContinuousSMul G X := ⟨continuous_action_of_stableNeighbourhoods⟩
  have he : compactSaturation (G := G) K = (Set.univ : Set G) • K := by
    ext x
    constructor
    · rintro ⟨⟨g, y⟩, ⟨_, hy⟩, rfl⟩
      exact Set.smul_mem_smul trivial hy
    · rintro ⟨g, _, y, hy, rfl⟩
      exact ⟨(g, y), ⟨trivial, hy⟩, rfl⟩
  rw [he]
  exact hK.smul_left_of_isCompact isCompact_univ

/-- Assemble group-indexed ordinary rows into a global indexed family. -/
def familyUnrow (A : X → ModuleCat.{u} R) :
    (functionRepresentation R G (compactRows A)).IntertwiningMap
      (CompactSections.globalRepresentation (CoinducedFamilies.presheaf A)) where
  toLinearMap :=
    { toFun f g y := (f g).val ⟨y.val, trivial⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

/-- Finite collections of compact rows assemble to a compact indexed section. -/
theorem isCompact_support_familyUnrow [CompactSpace G] [HasStableNeighbourhoods G X]
    (A : X → ModuleCat.{u} R) (f : G → compactRows A) (hf : (Set.range f).Finite) :
    IsCompact (Langlands.Sheaf.CompactSupport.support
      (CompactSections.ordinary (CoinducedFamilies.presheaf A)) (familyUnrow A f)) := by
  classical
  let K : Set X := ⋃ r ∈ Set.range f,
    Langlands.Sheaf.CompactSupport.support (ordinaryFamilies A) r.val
  have hKcompact : IsCompact K := hf.isCompact_biUnion fun r _ => r.property
  have hKclosed : IsClosed K := hf.isClosed_biUnion fun r _ =>
    Langlands.Sheaf.CompactSupport.isClosed_support _ _
  apply (isCompact_compactSaturation (G := G) hKcompact).of_isClosed_subset
    (Langlands.Sheaf.CompactSupport.isClosed_support _ _)
  intro x hx
  by_contra hnot
  apply hx
  apply (CompactSections.germ_zero_iff (CoinducedFamilies.presheaf A) _ x).2
  let U : ActionOpens G X :=
    ⟨⟨(compactSaturation (G := G) K)ᶜ, (isClosed_compactSaturation hKclosed).isOpen_compl⟩⟩
  refine ⟨U, hnot, ?_⟩
  funext g y
  have hrowzero : (ordinaryFamilies A).Γgerm y.val (f g).val = 0 := by
    by_contra hne
    have hyK : y.val ∈ K := Set.mem_iUnion.2 ⟨f g,
      Set.mem_iUnion.2 ⟨⟨g, rfl⟩, hne⟩⟩
    have hynot : g • y.val ∉ compactSaturation (G := G) K := y.property
    exact hynot ⟨(g, y.val), ⟨trivial, hyK⟩, rfl⟩
  exact (CoinducedFamilies.presheaf_map_inclusionHom_apply A le_top
    (familyUnrow A f) g y.val y.property).trans
      (ordinaryFamilies_value_zero A (f g).val y.val hrowzero)

/-- Smooth compact indexed families give uniformly smooth functions of compact rows. -/
def smoothCompactFamilyRows (A : X → ModuleCat.{u} R) :
    (SmoothCompactSections.representation (CoinducedFamilies.presheaf A)).IntertwiningMap
      (Langlands.smoothPart (functionRepresentation R G (compactRows A))) :=
  Langlands.smoothMap (compactFamilyRows A)

/-- For a compact group, reading compact rows is bijective on smooth vectors. -/
theorem smoothCompactFamilyRows_bijective [CompactSpace G] [HasStableNeighbourhoods G X]
    (A : X → ModuleCat.{u} R) : Function.Bijective (smoothCompactFamilyRows (G := G) A) := by
  constructor
  · intro s t h
    apply Subtype.ext
    apply Subtype.ext
    funext g y
    have hrow := congrFun (congrArg Subtype.val h) g
    exact congrFun (congrArg Subtype.val hrow) ⟨y.val, trivial⟩
  · intro f
    let t := Langlands.smoothMap (familyUnrow A) f
    have hc : IsCompact (Langlands.Sheaf.CompactSupport.support
        (CompactSections.ordinary (CoinducedFamilies.presheaf A)) t.val) :=
      isCompact_support_familyUnrow A f.val (cofree_finite_range (compactRows A) f)
    obtain ⟨s, hs⟩ := (SmoothCompactSections.exists_preimage_iff
      (CoinducedFamilies.presheaf A) t.val).2 ⟨hc, t.property⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext y
    change familyRow A s.val.val g y = (f.val g).val y
    rw [hs]
    rfl

/-- Smooth compact indexed families are the cofree representation on compact rows. -/
def compactFamiliesCofreeIso [CompactSpace G] [HasStableNeighbourhoods G X]
    (A : X → ModuleCat.{u} R) :
    (SmoothCompactSections.smoothFunctor R G X).obj (CoinducedFamilies.sheaf A) ≅
      cofreeObj R G (compactRows A) :=
  SmoothRep.mkIso ((smoothCompactFamilyRows A).ofBijective
    (smoothCompactFamilyRows_bijective A))

end Langlands.Cohomology.EquivariantComposite
