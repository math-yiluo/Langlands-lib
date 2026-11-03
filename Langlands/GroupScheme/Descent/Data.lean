import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Actual Čech descent data for group schemes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

namespace Langlands.GroupScheme.Descent

variable {B S T U : Scheme.{u}}

/-- The actual double overlap of a morphism of schemes. -/
abbrev Overlap (p : S ⟶ B) : Scheme.{u} := pullback p p

/-- First projection from the double overlap. -/
abbrev fst (p : S ⟶ B) : Overlap p ⟶ S := pullback.fst p p

/-- Second projection from the double overlap. -/
abbrev snd (p : S ⟶ B) : Overlap p ⟶ S := pullback.snd p p

/-- The triple overlap, with its middle coordinate identified by a pullback. -/
abbrev Triple (p : S ⟶ B) : Scheme.{u} := pullback (snd p) (fst p)

/-- Projection to coordinates 1 and 2. -/
abbrev p12 (p : S ⟶ B) : Triple p ⟶ Overlap p := pullback.fst (snd p) (fst p)

/-- Projection to coordinates 2 and 3. -/
abbrev p23 (p : S ⟶ B) : Triple p ⟶ Overlap p := pullback.snd (snd p) (fst p)

/-- The first coordinate of the triple overlap. -/
abbrev p1 (p : S ⟶ B) : Triple p ⟶ S := p12 p ≫ fst p

/-- The second coordinate of the triple overlap. -/
abbrev p2 (p : S ⟶ B) : Triple p ⟶ S := p12 p ≫ snd p

/-- The third coordinate of the triple overlap. -/
abbrev p3 (p : S ⟶ B) : Triple p ⟶ S := p23 p ≫ snd p

@[reassoc (attr := simp)] theorem p23_fst (p : S ⟶ B) :
    p23 p ≫ fst p = p2 p := pullback.condition.symm

/-- Projection to coordinates 1 and 3. -/
def p13 (p : S ⟶ B) : Triple p ⟶ Overlap p :=
  pullback.lift (p1 p) (p3 p) (by
    calc
      p1 p ≫ p = p2 p ≫ p := by
        dsimp [p1, p2]
        rw [Category.assoc, pullback.condition, ← Category.assoc]
      _ = p23 p ≫ fst p ≫ p := by rw [← Category.assoc, p23_fst]
      _ = p3 p ≫ p := by
        dsimp [p3]
        rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)] theorem p13_fst (p : S ⟶ B) :
    p13 p ≫ fst p = p1 p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem p13_snd (p : S ⟶ B) :
    p13 p ≫ snd p = p3 p := pullback.lift_snd _ _ _

/-- Iterated actual pullback compared to a specified equal composite pullback. -/
def pullbackComparison (f : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S)
    (h : q ≫ f = r) (G : GroupScheme S) :
    (baseChange q).obj ((baseChange f).obj G) ≅ (baseChange r).obj G :=
  (baseChangeCompIso f q G).symm ≪≫
    eqToIso (congrArg (fun k => (baseChange k).obj G) h)

/-- The comparison preserves the projection to the original group scheme. -/
@[reassoc (attr := simp)] theorem pullbackComparison_hom_fst
    (f : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S) (h : q ≫ f = r) (G : GroupScheme S) :
    (pullbackComparison f q r h G).hom.hom.hom.left ≫ pullback.fst G.X.hom r =
      pullback.fst ((baseChange f).obj G).X.hom q ≫ pullback.fst G.X.hom f := by
  subst r
  simp [pullbackComparison]

/-- The inverse comparison preserves the same original projection. -/
@[reassoc (attr := simp)] theorem pullbackComparison_inv_fst
    (f : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S) (h : q ≫ f = r) (G : GroupScheme S) :
    (pullbackComparison f q r h G).inv.hom.hom.left ≫
        pullback.fst ((baseChange f).obj G).X.hom q ≫ pullback.fst G.X.hom f =
      pullback.fst G.X.hom r := by
  rw [← pullbackComparison_hom_fst f q r h G, ← Category.assoc]
  change ((pullbackComparison f q r h G).inv ≫
    (pullbackComparison f q r h G).hom).hom.hom.left ≫ _ = _
  simp

/-- The direct/iterated comparison is natural in the group scheme. -/
@[reassoc] theorem pullbackComparison_naturality
    (f : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S) (h : q ≫ f = r)
    {G H : GroupScheme S} (a : G ⟶ H) :
    (baseChange q).map ((baseChange f).map a) ≫ (pullbackComparison f q r h H).hom =
      (pullbackComparison f q r h G).hom ≫ (baseChange r).map a := by
  subst r
  exact ((Functor.mapGrpNatIso (Over.pullbackComp q f)) ≪≫
    Functor.mapGrpCompIso).inv.naturality a

/-- Pull a morphism back, expressing its endpoints as direct pullbacks. -/
def pullHom (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s) {G H : GroupScheme S}
    (a : (baseChange f).obj G ⟶ (baseChange g).obj H) :
    (baseChange r).obj G ⟶ (baseChange s).obj H :=
  (pullbackComparison f q r hf G).inv ≫ (baseChange q).map a ≫
    (pullbackComparison g q s hg H).hom

@[simp] theorem pullHom_id (q : U ⟶ T) (f : T ⟶ S) (r : U ⟶ S)
    (hf : q ≫ f = r) (G : GroupScheme S) :
    pullHom q hf hf (𝟙 ((baseChange f).obj G)) = 𝟙 _ := by
  simp [pullHom]

@[reassoc] theorem pullHom_comp (q : U ⟶ T) {f g h : T ⟶ S} {r s t : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s) (hh : q ≫ h = t)
    {G H I : GroupScheme S}
    (a : (baseChange f).obj G ⟶ (baseChange g).obj H)
    (b : (baseChange g).obj H ⟶ (baseChange h).obj I) :
    pullHom q hf hh (a ≫ b) = pullHom q hf hg a ≫ pullHom q hg hh b := by
  simp [pullHom, Functor.map_comp]

/-- Pulling a base-changed homomorphism back gives its direct base change. -/
@[simp] theorem pullHom_map (q : U ⟶ T) (f : T ⟶ S) (r : U ⟶ S)
    (hf : q ≫ f = r) {G H : GroupScheme S} (a : G ⟶ H) :
    pullHom q hf hf ((baseChange f).map a) = (baseChange r).map a := by
  simp only [pullHom, pullbackComparison_naturality, Iso.inv_hom_id_assoc]

@[reassoc] private theorem baseChange_map_fst (f : T ⟶ S) {G H : GroupScheme S} (a : G ⟶ H) :
    ((baseChange f).map a).hom.hom.left ≫ pullback.fst H.X.hom f =
      pullback.fst G.X.hom f ≫ a.hom.hom.left := by
  exact pullback.lift_fst _ _ _

private theorem pullHom_preserves_projection (p : S ⟶ B) (C : GroupScheme B)
    (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s)
    (a : (baseChange f).obj ((baseChange p).obj C) ⟶
      (baseChange g).obj ((baseChange p).obj C))
    (ha : a.hom.hom.left ≫ pullback.fst ((baseChange p).obj C).X.hom g ≫
      pullback.fst C.X.hom p =
      pullback.fst ((baseChange p).obj C).X.hom f ≫ pullback.fst C.X.hom p) :
    (pullHom q hf hg a).hom.hom.left ≫
        pullback.fst ((baseChange p).obj C).X.hom s ≫ pullback.fst C.X.hom p =
      pullback.fst ((baseChange p).obj C).X.hom r ≫ pullback.fst C.X.hom p := by
  simp only [pullHom, Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  rw [pullbackComparison_hom_fst_assoc, baseChange_map_fst_assoc]
  simp only [ha]
  exact pullbackComparison_inv_fst_assoc f q r hf ((baseChange p).obj C)
    (pullback.fst C.X.hom p)

private theorem hom_ext_original (p : S ⟶ B) (C : GroupScheme B) (r : T ⟶ S)
    {G : GroupScheme T} {a b : G ⟶ (baseChange r).obj ((baseChange p).obj C)}
    (h : a.hom.hom.left ≫ pullback.fst ((baseChange p).obj C).X.hom r ≫
        pullback.fst C.X.hom p =
      b.hom.hom.left ≫ pullback.fst ((baseChange p).obj C).X.hom r ≫
        pullback.fst C.X.hom p) : a = b := by
  apply (cancel_mono (pullbackComparison p r (r ≫ p) rfl C).hom).mp
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      pullbackComparison_hom_fst] using h
  · exact (Over.w (a ≫ (pullbackComparison p r (r ≫ p) rfl C).hom).hom.hom).trans
      (Over.w (b ≫ (pullbackComparison p r (r ≫ p) rfl C).hom).hom.hom).symm

/-- Pull an isomorphism back, with the direct-pullback comparisons explicit. -/
def pullIso (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s) {G H : GroupScheme S}
    (e : (baseChange f).obj G ≅ (baseChange g).obj H) :
    (baseChange r).obj G ≅ (baseChange s).obj H :=
  (pullbackComparison f q r hf G).symm ≪≫ (baseChange q).mapIso e ≪≫
    pullbackComparison g q s hg H

@[simp] theorem pullIso_hom (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s) {G H : GroupScheme S}
    (e : (baseChange f).obj G ≅ (baseChange g).obj H) :
    (pullIso q hf hg e).hom = pullHom q hf hg e.hom := rfl

/-- An overlap isomorphism transports coordinate 1 to coordinate 2. -/
abbrev OverlapIso (p : S ⟶ B) (G : GroupScheme S) :=
  (baseChange (fst p)).obj G ≅ (baseChange (snd p)).obj G

/-- The overlap isomorphism on coordinates 1 and 2 of the triple overlap. -/
abbrev iso12 {p : S ⟶ B} {G : GroupScheme S} (e : OverlapIso p G) :=
  pullIso (p12 p) (rfl : p12 p ≫ fst p = p1 p) (rfl : p12 p ≫ snd p = p2 p) e

/-- The overlap isomorphism on coordinates 2 and 3 of the triple overlap. -/
abbrev iso23 {p : S ⟶ B} {G : GroupScheme S} (e : OverlapIso p G) :=
  pullIso (p23 p) (p23_fst p) (rfl : p23 p ≫ snd p = p3 p) e

/-- The overlap isomorphism on coordinates 1 and 3 of the triple overlap. -/
abbrev iso13 {p : S ⟶ B} {G : GroupScheme S} (e : OverlapIso p G) :=
  pullIso (p13 p) (p13_fst p) (p13_snd p) e

/-- First transport 1 to 2 and then 2 to 3, or transport 1 directly to 3. -/
def Cocycle {p : S ⟶ B} {G : GroupScheme S} (e : OverlapIso p G) : Prop :=
  (iso12 e).hom ≫ (iso23 e).hom = (iso13 e).hom

/-- Actual group-scheme Čech data contain an overlap isomorphism and its cocycle only. -/
structure Datum (p : S ⟶ B) (G : GroupScheme S) where
  /-- The actual group-scheme isomorphism from first pullback to second pullback. -/
  overlap : OverlapIso p G
  /-- The triple-overlap cocycle. -/
  cocycle : Cocycle overlap

@[ext] theorem Datum.ext {p : S ⟶ B} {G : GroupScheme S} {D E : Datum p G}
    (h : D.overlap = E.overlap) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- An actual group-scheme homomorphism respects the supplied descent data. -/
def Compatible {p : S ⟶ B} {G H : GroupScheme S}
    (D : Datum p G) (E : Datum p H) (f : G ⟶ H) : Prop :=
  (baseChange (fst p)).map f ≫ E.overlap.hom =
    D.overlap.hom ≫ (baseChange (snd p)).map f

@[simp] theorem compatible_id {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G) :
    Compatible D D (𝟙 G) := by simp [Compatible]

theorem Compatible.comp {p : S ⟶ B} {G H I : GroupScheme S}
    {D : Datum p G} {E : Datum p H} {F : Datum p I} {f : G ⟶ H} {g : H ⟶ I}
    (hf : Compatible D E f) (hg : Compatible E F g) : Compatible D F (f ≫ g) := by
  dsimp [Compatible] at *
  simp only [Functor.map_comp, Category.assoc]
  rw [hg, ← Category.assoc, hf, Category.assoc]

/-- Inverse isomorphisms respect the data whenever the forward isomorphism does. -/
theorem Compatible.inv {p : S ⟶ B} {G H : GroupScheme S}
    {D : Datum p G} {E : Datum p H} (e : G ≅ H)
    (he : Compatible D E e.hom) : Compatible E D e.inv := by
  dsimp [Compatible] at *
  rw [← cancel_mono ((baseChange (snd p)).map e.hom), Category.assoc,
    Category.assoc, Iso.map_inv_hom_id, Category.comp_id,
    ← cancel_epi ((baseChange (fst p)).map e.hom),
    Iso.map_hom_inv_id_assoc, he]

/-- Transfer an overlap isomorphism along a group-scheme isomorphism. -/
def transportOverlap {p : S ⟶ B} {G H : GroupScheme S}
    (D : Datum p G) (e : G ≅ H) : OverlapIso p H :=
  (baseChange (fst p)).mapIso e.symm ≪≫ D.overlap ≪≫
    (baseChange (snd p)).mapIso e

private theorem pullHom_transportOverlap {p : S ⟶ B} {G H : GroupScheme S}
    (D : Datum p G) (e : G ≅ H) (q : T ⟶ Overlap p) (r s : T ⟶ S)
    (hr : q ≫ fst p = r) (hs : q ≫ snd p = s) :
    pullHom q hr hs (transportOverlap D e).hom =
      (baseChange r).map e.inv ≫ pullHom q hr hs D.overlap.hom ≫
        (baseChange s).map e.hom := by
  change pullHom q hr hs
    ((baseChange (fst p)).map e.inv ≫ D.overlap.hom ≫
      (baseChange (snd p)).map e.hom) = _
  rw [pullHom_comp q hr hr hs, pullHom_comp q hr hs hs, pullHom_map, pullHom_map]

/-- Transport of a datum has the conjugate overlap isomorphism. -/
def Datum.transport {p : S ⟶ B} {G H : GroupScheme S}
    (D : Datum p G) (e : G ≅ H) : Datum p H where
  overlap := transportOverlap D e
  cocycle := by
    change pullHom (p12 p) rfl rfl _ ≫ pullHom (p23 p) (p23_fst p) rfl _ =
      pullHom (p13 p) (p13_fst p) (p13_snd p) _
    simp only [pullHom_transportOverlap, Category.assoc]
    rw [Iso.map_hom_inv_id_assoc]
    have hc := D.cocycle
    change pullHom (p12 p) rfl rfl _ ≫ pullHom (p23 p) (p23_fst p) rfl _ =
      pullHom (p13 p) (p13_fst p) (p13_snd p) _ at hc
    rw [← Category.assoc _ _ ((baseChange (p3 p)).map e.hom), hc]

/-- The isomorphism used to transport data is compatible. -/
theorem Datum.compatible_transport {p : S ⟶ B} {G H : GroupScheme S}
    (D : Datum p G) (e : G ≅ H) : Compatible D (D.transport e) e.hom := by
  simp [Compatible, Datum.transport, transportOverlap]

/-- The reverse of the transporting isomorphism is compatible. -/
theorem Datum.compatible_transport_inv {p : S ⟶ B} {G H : GroupScheme S}
    (D : Datum p G) (e : G ≅ H) : Compatible (D.transport e) D e.inv :=
  (D.compatible_transport e).inv e

@[simp] theorem Datum.transport_refl {p : S ⟶ B} {G : GroupScheme S}
    (D : Datum p G) : D.transport (Iso.refl G) = D := by
  apply Datum.ext
  apply Iso.ext
  simp [Datum.transport, transportOverlap]

theorem Datum.transport_trans {p : S ⟶ B} {G H I : GroupScheme S}
    (D : Datum p G) (e : G ≅ H) (f : H ≅ I) :
    (D.transport e).transport f = D.transport (e ≪≫ f) := by
  apply Datum.ext
  apply Iso.ext
  simp [Datum.transport, transportOverlap]

@[simp] theorem Datum.transport_symm {p : S ⟶ B} {G H : GroupScheme S}
    (D : Datum p G) (e : G ≅ H) : (D.transport e).transport e.symm = D := by
  rw [Datum.transport_trans]
  simp

/-- A compatible isomorphism identifies the target datum with the transported datum. -/
theorem Datum.transport_eq {p : S ⟶ B} {G H : GroupScheme S}
    {D : Datum p G} {E : Datum p H} (e : G ≅ H)
    (he : Compatible D E e.hom) : D.transport e = E := by
  apply Datum.ext
  apply Iso.ext
  change (baseChange (fst p)).map e.inv ≫
    D.overlap.hom ≫ (baseChange (snd p)).map e.hom = E.overlap.hom
  rw [← he, Iso.map_inv_hom_id_assoc]

/-- The canonical overlap identification of a group scheme pulled back from the base. -/
def canonicalOverlap (p : S ⟶ B) (C : GroupScheme B) :
    OverlapIso p ((baseChange p).obj C) :=
  pullbackComparison p (fst p) (fst p ≫ p) rfl C ≪≫
    (pullbackComparison p (snd p) (fst p ≫ p) pullback.condition.symm C).symm

/-- Canonical overlap transport does not change the projection to the original group. -/
@[reassoc] theorem canonicalOverlap_fst (p : S ⟶ B) (C : GroupScheme B) :
    (canonicalOverlap p C).hom.hom.hom.left ≫
        pullback.fst ((baseChange p).obj C).X.hom (snd p) ≫ pullback.fst C.X.hom p =
      pullback.fst ((baseChange p).obj C).X.hom (fst p) ≫ pullback.fst C.X.hom p := by
  change ((pullbackComparison p (fst p) (fst p ≫ p) rfl C).hom.hom.hom.left ≫
    (pullbackComparison p (snd p) (fst p ≫ p) pullback.condition.symm C).inv.hom.hom.left)
      ≫ _ ≫ _ = _
  simp only [Category.assoc, pullbackComparison_inv_fst, pullbackComparison_hom_fst]

/-- Pulling back the canonical overlap still preserves the original projection. -/
@[reassoc] theorem pullHom_canonicalOverlap_fst (p : S ⟶ B) (C : GroupScheme B)
    (q : T ⟶ Overlap p) (r s : T ⟶ S)
    (hr : q ≫ fst p = r) (hs : q ≫ snd p = s) :
    (pullHom q hr hs (canonicalOverlap p C).hom).hom.hom.left ≫
        pullback.fst ((baseChange p).obj C).X.hom s ≫ pullback.fst C.X.hom p =
      pullback.fst ((baseChange p).obj C).X.hom r ≫ pullback.fst C.X.hom p :=
  pullHom_preserves_projection p C q hr hs _ (canonicalOverlap_fst p C)

/-- The canonical datum on the actual pullback of a group scheme over the base. -/
def canonicalDatum (p : S ⟶ B) (C : GroupScheme B) :
    Datum p ((baseChange p).obj C) where
  overlap := canonicalOverlap p C
  cocycle := by
    apply hom_ext_original p C (p3 p)
    change (pullHom (p12 p) rfl rfl (canonicalOverlap p C).hom ≫
      pullHom (p23 p) (p23_fst p) rfl (canonicalOverlap p C).hom).hom.hom.left ≫ _ ≫ _ =
      (pullHom (p13 p) (p13_fst p) (p13_snd p) (canonicalOverlap p C).hom).hom.hom.left
        ≫ _ ≫ _
    simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      pullHom_canonicalOverlap_fst]

/-- Base change of a homomorphism respects the canonical descent data. -/
theorem canonicalDatum_compatible (p : S ⟶ B) {C D : GroupScheme B} (a : C ⟶ D) :
    Compatible (canonicalDatum p C) (canonicalDatum p D) ((baseChange p).map a) := by
  apply hom_ext_original p D (snd p)
  simp only [canonicalDatum, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    canonicalOverlap_fst, baseChange_map_fst, baseChange_map_fst_assoc,
    canonicalOverlap_fst_assoc]

/-- A solution is a descended object with a compatible actual pullback isomorphism. -/
structure Solution {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G) where
  /-- The actual group scheme over the base. -/
  obj : GroupScheme B
  /-- Its actual base change identified with the given group scheme. -/
  iso : (baseChange p).obj obj ≅ G
  /-- The identification respects the canonical and supplied descent data. -/
  compatible : Compatible (canonicalDatum p obj) D iso.hom

/-- The canonical datum has its tautological solution. -/
def canonicalSolution (p : S ⟶ B) (C : GroupScheme B) :
    Solution (canonicalDatum p C) where
  obj := C
  iso := Iso.refl _
  compatible := compatible_id _

/-- Compose a solution with any compatible group-scheme isomorphism. -/
def Solution.mapIso {p : S ⟶ B} {G H : GroupScheme S}
    {D : Datum p G} {E : Datum p H} (s : Solution D) (e : G ≅ H)
    (he : Compatible D E e.hom) : Solution E where
  obj := s.obj
  iso := s.iso ≪≫ e
  compatible := s.compatible.comp he

/-- Transport a solution along the same isomorphism used to transport its datum. -/
def Solution.transport {p : S ⟶ B} {G H : GroupScheme S}
    {D : Datum p G} (s : Solution D) (e : G ≅ H) : Solution (D.transport e) :=
  s.mapIso e (D.compatible_transport e)

end Langlands.GroupScheme.Descent
