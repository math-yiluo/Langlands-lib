/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Comparing the two geometric finiteness predicates

Source: Stacks Project, Tag 04FN.
(blueprint: lem-galois-finite-stalks-comparison)
-/

@[expose] public section

universe v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem bijective_geometric_lifts {Y : Scheme.{v}}
    {K L : Type v} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L]
    (j : Spec (.of L) ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ Y) (V : Y.Etale) :
    Function.Bijective (fun t : (pointSmallEtale s).fiber.obj V ↦
      (Over.homMk (j ≫ t.left) (by
        change j ≫ t.left ≫ V.hom = j ≫ s
        exact congrArg (j ≫ ·) (Over.w t)) :
        (pointSmallEtale (j ≫ s)).fiber.obj V)) := by
  have : Surjective j := ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  constructor
  · intro a b hab
    apply Over.OverMorphism.ext
    exact Scheme.Hom.ext_of_surjective_of_formallyUnramified j V.hom
      ((Over.w a).trans (Over.w b).symm) (congrArg Over.Hom.left hab)
  · intro t
    let W := pullback V.hom s
    let q : W ⟶ Spec (.of K) := pullback.snd V.hom s
    let l : Spec (.of L) ⟶ W := pullback.lift t.left j (Over.w t)
    have hl : l ≫ q = j := pullback.lift_snd _ _ _
    obtain ⟨r, hr, hx⟩ := exists_fac_of_etale_of_isSepClosed q (𝟙 _) (l default)
      (Subsingleton.elim _ _)
    have : Etale (r ≫ q) := by rw [hr]; infer_instance
    have : Etale r := Etale.of_comp r q
    have : Mono r := mono_of_mono_fac hr
    have : IsOpenImmersion r := IsOpenImmersion.of_flat_of_mono r
    have hrl : Set.range l.base ⊆ Set.range r.base := by
      rintro _ ⟨x, rfl⟩
      exact ⟨default, hx.trans (congrArg l.base (Subsingleton.elim _ _))⟩
    let k := IsOpenImmersion.lift r l hrl
    have hk : k ≫ r = l := IsOpenImmersion.lift_fac r l hrl
    have hk' : k = j := by
      calc
        k = k ≫ r ≫ q := by rw [hr, Category.comp_id]
        _ = j := by rw [← Category.assoc, hk, hl]
    refine ⟨Over.homMk (r ≫ pullback.fst V.hom s) (by
      change (r ≫ pullback.fst V.hom s) ≫ V.hom = s
      rw [Category.assoc, pullback.condition, ← Category.assoc, hr, Category.id_comp]), ?_⟩
    apply Over.OverMorphism.ext
    change j ≫ r ≫ pullback.fst V.hom s = t.left
    calc
      j ≫ r ≫ pullback.fst V.hom s = k ≫ r ≫ pullback.fst V.hom s :=
        congrArg (fun z ↦ z ≫ r ≫ pullback.fst V.hom s) hk'.symm
      _ = l ≫ pullback.fst V.hom s := by rw [← Category.assoc, hk]
      _ = t.left := pullback.lift_fst _ _ _

/-- Finiteness at algebraically closed geometric points implies the source library's
finiteness predicate, which tests all separably closed geometric points.
Source: Stacks Project, Tag 04FN (invariance under extension of geometric points).
(blueprint: lem-galois-finite-stalks-comparison)

Proof: Given a separably closed field Ω and a geometric point s, extend s along
Spec of an algebraic closure of Ω. Every étale neighbourhood has exactly the
same lifts of the two geometric points. Indeed, on its pullback to Spec Ω the
point picked out by a lift has a section, since Ω is separably closed. That
section is an open immersion, and the extended lift factors through it because
Spec of a field is a singleton. This gives surjectivity on lifts. Injectivity
follows from the open diagonal of the étale morphism and surjectivity of the
field-extension morphism. These bijections commute with morphisms of
neighbourhoods and identify their categories of pointed neighbourhoods. Taking
the colimit of the values of E
therefore identifies the two stalks. The extended point has a finite stalk by the
hypothesis. Transfer finiteness across this identification; in Type, finite is
equivalent to ConcreteCategory.IsFinitelyGenerated. This gives every field of
IsFiniteSheaf. The argument also applies to empty stalks; on an empty scheme there
are no geometric points and both assertions are vacuous. -/
theorem isFiniteSheaf_of_finite_algClosed_stalks {Y : Scheme.{v}}
    (E : Sheaf Y.smallEtaleTopology (Type (v + 1)))
    (h : ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (v + 1))).obj E)) :
    IsFiniteSheaf E := by
  classical
  constructor
  intro K _ _ s
  let L := AlgebraicClosure K
  let j : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let e : (pointSmallEtale s).fiber ≅ (pointSmallEtale (j ≫ s)).fiber :=
    NatIso.ofComponents (fun V ↦ Equiv.toIso
      (Equiv.ofBijective _ (bijective_geometric_lifts j s V))) (by
        intro V V' f
        ext t
        apply Over.OverMorphism.ext
        change (j ≫ t.left) ≫ f.left = j ≫ (t.left ≫ f.left)
        exact Category.assoc j t.left f.left)
  let ε := GrothendieckTopology.Point.sheafFiberIso
    (GrothendieckTopology.Point.isoMk e) (A := Type (v + 1))
  have := h L (j ≫ s)
  have := Finite.of_equiv _ (ε.app E).toEquiv.symm
  exact (ConcreteCategory.isFinitelyGenerated_iff_finite _).2 inferInstance

end AlgebraicGeometry.Scheme
