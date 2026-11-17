import Langlands.GroupScheme.OuterIsomorphismScheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Comparison of supplied outer-isomorphism quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.OuterIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  (O : OuterIsomorphismScheme I a)

/-- An invariant morphism agrees on every relation of the class morphism. -/
theorem invariant_relation {P : Over S} (f : I.parameter ⟶ P)
    (hf : ∀ (T : Over S) (d : T ⟶ A.X) (p : T ⟶ I.parameter),
      (lift d p ≫ I.actionHom a) ≫ f = p ≫ f)
    {T : Over S} (p q : T ⟶ I.parameter)
    (hpq : p ≫ O.classMap = q ≫ O.classMap) :
    p ≫ f = q ≫ f := by
  obtain ⟨d, hd, _⟩ := O.orbit T p q hpq
  exact (hf T d p).symm.trans (congrArg (fun z => z ≫ f) hd)

/-- The same relation equality holds for morphisms of underlying schemes. -/
theorem invariant_relation_left {P : Over S} (f : I.parameter ⟶ P)
    (hf : ∀ (T : Over S) (d : T ⟶ A.X) (p : T ⟶ I.parameter),
      (lift d p ≫ I.actionHom a) ≫ f = p ≫ f)
    {T : Scheme.{u}} (r s : T ⟶ I.parameter.left)
    (hrs : r ≫ O.classMap.left = s ≫ O.classMap.left) :
    r ≫ f.left = s ≫ f.left := by
  have hs : s ≫ I.parameter.hom = r ≫ I.parameter.hom := by
    rw [← Over.w O.classMap, ← Category.assoc, ← Category.assoc, hrs]
  let r₀ : Over.mk (r ≫ I.parameter.hom) ⟶ I.parameter := Over.homMk r rfl
  let s₀ : Over.mk (r ≫ I.parameter.hom) ⟶ I.parameter := Over.homMk s hs
  exact congrArg (fun z => z.left)
    (O.invariant_relation f hf r₀ s₀ (Over.OverMorphism.ext hrs))

/-- Every invariant relative morphism descends along the supplied fpqc class map. -/
def descend {P : Over S} (f : I.parameter ⟶ P)
    (hf : ∀ (T : Over S) (d : T ⟶ A.X) (p : T ⟶ I.parameter),
      (lift d p ≫ I.actionHom a) ≫ f = p ≫ f) :
    O.parameter ⟶ P := by
  let g : O.parameter.left ⟶ P.left :=
    EffectiveEpi.desc O.classMap.left f.left (O.invariant_relation_left f hf)
  have hg : O.classMap.left ≫ g = f.left :=
    EffectiveEpi.fac O.classMap.left f.left (O.invariant_relation_left f hf)
  exact Over.homMk g (by
    apply (cancel_epi O.classMap.left).mp
    rw [← Category.assoc, hg, Over.w f, Over.w O.classMap])

@[reassoc (attr := simp)]
theorem classMap_descend {P : Over S} (f : I.parameter ⟶ P)
    (hf : ∀ (T : Over S) (d : T ⟶ A.X) (p : T ⟶ I.parameter),
      (lift d p ≫ I.actionHom a) ≫ f = p ≫ f) :
    O.classMap ≫ O.descend f hf = f := by
  apply Over.OverMorphism.ext
  exact EffectiveEpi.fac O.classMap.left f.left (O.invariant_relation_left f hf)

/-- Equality after the fpqc class map detects equality of relative morphisms. -/
theorem hom_ext {P : Over S} {f g : O.parameter ⟶ P}
    (h : O.classMap ≫ f = O.classMap ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply (cancel_epi O.classMap.left).mp
  exact congrArg (fun z => z.left) h

/-- The class-map equation characterizes the descended morphism uniquely. -/
theorem descend_unique {P : Over S} (f : I.parameter ⟶ P)
    (hf : ∀ (T : Over S) (d : T ⟶ A.X) (p : T ⟶ I.parameter),
      (lift d p ≫ I.actionHom a) ≫ f = p ≫ f)
    (g : O.parameter ⟶ P) (hg : O.classMap ≫ g = f) :
    g = O.descend f hf :=
  O.hom_ext (hg.trans (O.classMap_descend f hf).symm)

/-- The canonical comparison of two supplied quotients of the same action. -/
def comparisonIso (O' : OuterIsomorphismScheme I a) :
    O.parameter ≅ O'.parameter where
  hom := O.descend O'.classMap O'.invariant
  inv := O'.descend O.classMap O.invariant
  hom_inv_id := O.hom_ext (by simp)
  inv_hom_id := O'.hom_ext (by simp)

@[reassoc (attr := simp)]
theorem classMap_comparisonIso_hom (O' : OuterIsomorphismScheme I a) :
    O.classMap ≫ (O.comparisonIso O').hom = O'.classMap :=
  O.classMap_descend O'.classMap O'.invariant

@[reassoc (attr := simp)]
theorem classMap_comparisonIso_inv (O' : OuterIsomorphismScheme I a) :
    O'.classMap ≫ (O.comparisonIso O').inv = O.classMap :=
  O'.classMap_descend O.classMap O.invariant

/-- The canonical comparison is the unique isomorphism respecting class maps. -/
theorem comparisonIso_unique (O' : OuterIsomorphismScheme I a)
    (e : O.parameter ≅ O'.parameter)
    (he : O.classMap ≫ e.hom = O'.classMap) :
    e = O.comparisonIso O' := by
  apply Iso.ext
  exact O.hom_ext (he.trans (O.classMap_comparisonIso_hom O').symm)

end Langlands.GroupScheme.OuterIsomorphismScheme

namespace Langlands.GroupScheme.FiniteGenericOuterClass

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  {O O' : OuterIsomorphismScheme I a} {T : Over S} {p : T ⟶ I.parameter}

/-- Transport a finite class carrier to any other supplied quotient of the same action. -/
def ofComparison (C : FiniteGenericOuterClass O p) :
    FiniteGenericOuterClass O' p where
  component := C.component
  classMap := C.classMap ≫ (O.comparisonIso O').hom
  genericPoint := C.genericPoint
  generic_class := by
    rw [← Category.assoc, C.generic_class, Category.assoc,
      O.classMap_comparisonIso_hom]

/-- Finite-carrier existence is independent of the supplied outer quotient. -/
theorem nonempty_iff_comparison :
    Nonempty (FiniteGenericOuterClass O p) ↔ Nonempty (FiniteGenericOuterClass O' p) :=
  ⟨fun ⟨C⟩ => ⟨C.ofComparison⟩, fun ⟨C⟩ => ⟨C.ofComparison⟩⟩

end Langlands.GroupScheme.FiniteGenericOuterClass
