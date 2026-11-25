module

import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import StacksFrontier.RingTheory.Flat.LocalConstruction
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Constructing flat ring maps

Two ways of realizing a prescribed residue field extension by a flat ring map.

The first (Stacks Tag 07NE) is finite free, and realizes a *finite* extension: for a commutative
ring `R`, a prime ideal `p ⊆ R` and a finite extension `L / κ(p)` of the residue field of `R` at
`p`, there are a commutative ring `S` and a finite free ring map `φ : R →+* S` such that `q := pS`
is prime, lies over `p`, and whose induced residue field extension `κ(q) / κ(p)` is isomorphic to
`L / κ(p)`.

The second (Stacks Tag 03C3) realizes an *arbitrary* extension, at the price of finite freeness:
for a local ring `(R, 𝔪, k)` and a field extension `K / k` there are a local ring `(R', 𝔪', k')`,
a flat local ring map `R → R'` with `𝔪' = 𝔪 R'`, and an isomorphism `k' ≅ K` of extensions of
`k`. So every extension of the residue field of a local ring is realized, with no change to the
maximal ideal, by a flat local extension of the ring itself.

## Main definitions

* `ResidueFieldAtPrime R p`: the residue field `κ(p)` of `R` at `p`; an abbreviation for
  `Ideal.ResidueField p`.
* `inducedResidueMap φ p q h`: the residue field extension `κ(p) →+* κ(q)` induced by
  `φ : R →+* S` at a prime `q` lying over `p`; `Ideal.ResidueField.map p q φ h`.
* `IsFiniteFree φ`: the ring map `φ : R →+* S` is finite free, i.e. `S` regarded as an
  `R`-module via `φ` is free of finite rank.
* `adjoinRootFracHom K g`: the base change of `AdjoinRoot g` along `algebraMap D K`, the ring
  map `AdjoinRoot g →+* AdjoinRoot (g.map (algebraMap D K))` fixing `D` and sending root to root.

## Main results

* `exists_isFiniteFree_residueField_equiv`: a finite extension of `κ(p)` is the residue field
  extension of a finite free
  ring map `R → S` at `q = pS`.
* `isFractionRing_adjoinRootFrac`: for `g` monic over a domain `D` whose image over `K = Frac D`
  is irreducible, the field `AdjoinRoot (g.map (algebraMap D K))` is a fraction field of the
  domain `AdjoinRoot g`.
* `IsLocalRing.exists_flat_residueField_algEquiv`: for a local ring `R` and a field extension `K`
  of its residue field there is a flat local `R`-algebra `R'` with `𝔪 R'` for its maximal ideal
  and with residue field `k`-isomorphic to `K`.

## Implementation notes

*The finite free case.* The extension `L / κ(p)` is encoded by `[Algebra (κ(p)) L]`, with
structure map `algebraMap (κ(p)) L`; the ideal `pS` is `Ideal.map φ p`; and "isomorphic as an
extension of `κ(p)`" means that the field isomorphism `Φ : κ(q) ≃+* L` satisfies
`Φ ∘ inducedResidueMap φ p q = algebraMap (κ(p)) L`.

*The general case is a transfinite assembly of monogenic steps.* The construction, which is no
part of the statement of 03C3, adjoins the elements of `K` one at a time. A monogenic step
`κ ⊆ κ(α)` over a local ring `(A, 𝔪_A, κ)` is realized by `A[x]` localized at the prime
`𝔪_A A[x]` when `α` is transcendental over `κ` (the residue field there is `κ(x)`), and by
`A[T] / (T ^ d + ∑ λ_i T ^ (d - i))` for a lift of the minimal polynomial of `α` when `α` is
algebraic over `κ`; a directed colimit of such extensions is again one, because flatness and the
formation of `𝔪 · (-)` both commute with directed colimits. Those steps and colimits are carried
out in `StacksFrontier/RingTheory/Flat/LocalConstruction.lean`, whose bookkeeping object is
`GoodLift A F`: a flat local `A`-algebra with `𝔪_{A'} = 𝔪_A A'` together with a `κ`-embedding
`ResidueField A' →+* F`. A good lift whose embedding is onto solves the problem.

*The recursion is categorical, not a well-founded recursion on the index.* A hand-rolled
recursion cannot state its own coherence: the transition map from stage `j` to stage `i` has a
type depending on the good lifts constructed at `j` and `i`, so the tower and the cocycle of its
legs have to be built simultaneously. Organizing good lifts into a category makes a coherent
directed system a functor and the cocycle functoriality, and Mathlib's transfinite iteration
`CategoryTheory.SmallObject.SuccStruct.iterationFunctor` then supplies the tower, including its
definition at limit stages. Morphisms of good lifts are not required to be flat: flatness of each
stage over the base is part of `GoodLift`, and the colimit engine asks only that the transition
maps be local, so morphisms compose without any flatness input.

*The local ring map of 03C3 is an algebra map.* The source's `R → R'` is `algebraMap R R'`, being
local is `IsLocalHom` and being flat is `Module.Flat R R'`; the `Algebra R R'`, `IsLocalRing R'`
and `IsLocalHom` binders are the lemma's preamble ("there exists a local ring and a local ring
map"), and the three conjuncts are flatness, `𝔪' = 𝔪 R'`, and `k' ≅ K` over `k`. No hypothesis
is imposed on `K / k`: it need not be algebraic, finitely generated or separable.

*`𝔪' = 𝔪 R'` and `k' ≅ K` are two conjuncts, not one.* `𝔪 R'` is
`(maximalIdeal R).map (algebraMap R R')`, and a local ring map always has `𝔪 R' ≤ 𝔪'`, so the
second conjunct is the assertion that `R' / 𝔪 R'` is already a field. Granted it, the third
conjunct is exactly that this field is `K` as an extension of `k`; the two are therefore
equivalent to the single statement that the closed fibre `k ⊗[R] R'` is `k`-isomorphic to `K`,
and are kept separate because that is the form in which the source and its users state them.

*Isomorphic as an extension of `k`.* `ResidueField R' ≃ₐ[ResidueField R] K` is an isomorphism of
`k`-algebras for the canonical `k`-algebra structure on `k'` induced by `algebraMap R R'`
(`IsLocalRing.ResidueField.instAlgebra`), so an abstract ring isomorphism `k' ≅ K` that does not
respect the two maps out of `k` does not satisfy it. Since a `k`-algebra map of fields is
injective, "isomorphic as an extension of `k`" and "`K` embeds in `k'` over `k` by a surjection"
are the same requirement, and the `≃ₐ` form is the usable one.

*The universes of 03C3.* `R : Type u` and `K : Type v` are independent and `R' : Type (max u v)`,
which is where the construction lands: it adjoins one element of `K` at a time to `R`, so `R'` has
cardinality at most `max #R #K ℵ₀`. The source states the lemma with `R` and `K` in one universe,
which is the case `v = u`. Since `GoodLift` is universe-monomorphic, the assembly is run over
`ULift.{v} R` and `ULift.{u} K` and its conclusion transported back along `ULift.ringEquiv`.

## References

* [StacksProject 07NE](https://stacks.math.columbia.edu/tag/07NE)
* [StacksProject 03C3](https://stacks.math.columbia.edu/tag/03C3)
* [StacksProject 09E0](https://stacks.math.columbia.edu/tag/09E0), the separable algebraic case
  of 03C3 as a colimit of finite étale extensions

## Tags

flat, flat ring map, flat local ring map, finite free, local ring, residue field,
field extension, monogenic extension
-/

@[expose] public section

open IsLocalRing

/-! ### The conclusion as a predicate, and the two reduction steps -/

/-! ### The monogenic step

The construction takes `S₁ = AdjoinRoot f`, `φ₁ = AdjoinRoot.of f`, for a monic `f ∈ R[X]`
whose reduction over `K = κ(p)` is the minimal polynomial of a denominator-cleared generator
`β` of the simple subextension `K⟮α⟯ = K⟮β⟯`. -/

/-! ### Realizing an arbitrary residue field extension by a flat local ring map

Good lifts of `A` towards `F` are organized into a category, in which a coherent directed system
is a functor and the colimits of `LocalConstruction.lean` are the colimits of well-ordered shapes;
adjoining one missing element of `F` is a successor structure on that category, and the transfinite
assembly is its iteration, run far enough that some stage's residue embedding is already onto.
-/

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace GoodLift

section Assembly

variable {A : Type w} [CommRing A] [IsLocalRing A] {F : Type w} [Field F]
  [Algebra (ResidueField A) F]

/-- A morphism of good lifts: a local ring map of the carriers which extends the maximal ideal,
commutes with the structure maps and is compatible with the embeddings into `F`. Flatness is not
required of a morphism: flatness of every stage over `A` is part of `GoodLift`, and the colimit
engine needs only locality of the transition maps. -/
private structure Hom (g h : GoodLift A F) : Type w where
  /-- the underlying ring map of carriers -/
  ψ : g.carrier →+* h.carrier
  /-- the ring map is local -/
  isLocal : IsLocalHom ψ
  /-- the maximal ideal of the target is generated by the image of the maximal ideal -/
  maxeq : maximalIdeal h.carrier = Ideal.map ψ (maximalIdeal g.carrier)
  /-- the ring map commutes with the structure maps from `A` -/
  φcomp : ψ.comp g.φ = h.φ
  /-- the induced map of residue fields is compatible with the embeddings into `F` -/
  ιcomp : h.ι.comp (@ResidueField.map _ _ _ _ _ _ ψ isLocal) = g.ι

/-- Two morphisms of good lifts with the same underlying ring map are equal: all other fields
are propositions. -/
private theorem Hom.ext' {g h : GoodLift A F} {f₁ f₂ : Hom g h} (H : f₁.ψ = f₂.ψ) :
    f₁ = f₂ := by
  cases f₁; cases f₂; subst H; rfl

/-- Good lifts of `A` towards `F` form a category, with `GoodLift.Hom` for its morphisms. -/
@[instance_reducible] private def category : Category.{w} (GoodLift A F) where
  Hom g h := Hom g h
  id g :=
    { ψ := RingHom.id g.carrier
      isLocal := ⟨fun _ ha => ha⟩
      maxeq := by rw [Ideal.map_id]
      φcomp := RingHom.id_comp _
      ιcomp := by rw [IsLocalRing.ResidueField.map_id, RingHom.comp_id] }
  comp {g h l} f₁ f₂ :=
    { ψ := f₂.ψ.comp f₁.ψ
      isLocal := by
        have := f₁.isLocal; have := f₂.isLocal; exact RingHom.isLocalHom_comp _ _
      maxeq := by rw [f₂.maxeq, f₁.maxeq, Ideal.map_map]
      φcomp := by rw [RingHom.comp_assoc, f₁.φcomp, f₂.φcomp]
      ιcomp := by
        have := f₁.isLocal; have := f₂.isLocal
        rw [IsLocalRing.ResidueField.map_comp f₁.ψ f₂.ψ, ← RingHom.comp_assoc, f₂.ιcomp,
          f₁.ιcomp] }
  id_comp _ := Hom.ext' (RingHom.comp_id _)
  comp_id _ := Hom.ext' (RingHom.id_comp _)
  assoc _ _ _ := Hom.ext' (RingHom.comp_assoc _ _ _).symm

attribute [local instance] category

/-- **Recognizing a morphism of good lifts on an exhausting family.** Let `ψ` be a ring map
`g.carrier →+* h.carrier` whose composite with a family of morphisms `p i : l i ⟶ g` is the
underlying map of a family of morphisms `q i : l i ⟶ h`, and let the images of the `p i` cover
`g.carrier`. Then `ψ` is a morphism of good lifts `g ⟶ h`.

This is what makes the colimit descent one lemma: the maximal-ideal and structure-map clauses
hold already at a single index, by `Ideal.map_map` and associativity, while locality and the
compatibility with the residue embeddings are clauses about elements, so for an element coming
from the index `i` they are the corresponding clauses for `p i` and `q i`. -/
private def Hom.ofExhaustive {I : Type*} {l : I → GoodLift A F} {g h : GoodLift A F}
    (p : ∀ i, Hom (l i) g) (q : ∀ i, Hom (l i) h) (ψ : g.carrier →+* h.carrier)
    (hfac : ∀ i, ψ.comp (p i).ψ = (q i).ψ) (hexh : ∀ z : g.carrier, ∃ i x, (p i).ψ x = z)
    (i₀ : I) : Hom g h where
  ψ := ψ
  isLocal := by
    refine ⟨fun z hz => ?_⟩
    obtain ⟨i, x, rfl⟩ := hexh z
    rw [show ψ ((p i).ψ x) = (q i).ψ x from DFunLike.congr_fun (hfac i) x] at hz
    have := (q i).isLocal
    exact (isUnit_of_map_unit (q i).ψ x hz).map (p i).ψ
  maxeq := by
    calc maximalIdeal h.carrier
        = Ideal.map (q i₀).ψ (maximalIdeal (l i₀).carrier) := (q i₀).maxeq
      _ = Ideal.map (ψ.comp (p i₀).ψ) (maximalIdeal (l i₀).carrier) := by rw [hfac]
      _ = Ideal.map ψ (Ideal.map (p i₀).ψ (maximalIdeal (l i₀).carrier)) :=
          (Ideal.map_map _ _).symm
      _ = Ideal.map ψ (maximalIdeal g.carrier) := by rw [← (p i₀).maxeq]
  φcomp := by
    rw [← (p i₀).φcomp, ← RingHom.comp_assoc, hfac i₀]
    exact (q i₀).φcomp
  ιcomp := by
    refine RingHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := residue_surjective (R := g.carrier) x
    obtain ⟨i, y, rfl⟩ := hexh z
    have hp := DFunLike.congr_fun (p i).ιcomp (residue (l i).carrier y)
    have hq := DFunLike.congr_fun (q i).ιcomp (residue (l i).carrier y)
    simp only [RingHom.coe_comp, Function.comp_apply, ResidueField.map_residue] at hp hq ⊢
    rw [show ψ ((p i).ψ y) = (q i).ψ y from DFunLike.congr_fun (hfac i) y, hq, hp]

/-- A morphism of good lifts enlarges the subfield of `F` cut out by the residue embedding. -/
private theorem range_ι_subset {g h : GoodLift A F} (f : Hom g h) :
    Set.range g.ι ⊆ Set.range h.ι := by
  rintro x ⟨y, rfl⟩
  refine ⟨@ResidueField.map _ _ _ _ _ _ f.ψ f.isLocal y, ?_⟩
  simpa using DFunLike.congr_fun f.ιcomp y

/-- Isomorphic good lifts cut out the same subfield of `F`. -/
private theorem range_ι_eq_of_iso {g h : GoodLift A F} (e : g ≅ h) :
    Set.range g.ι = Set.range h.ι :=
  Set.Subset.antisymm (range_ι_subset e.hom) (range_ι_subset e.inv)

/-- **Colimits of directed systems of good lifts.** A functor from a directed nonempty preorder
to good lifts has a colimit: its carrier is the colimit ring of the carriers, by the engine
`goodLift_colimit_chosen_noflat`, and a family of morphisms out of the stages descends to it by
`GoodLift.Hom.ofExhaustive`. -/
private theorem hasColimit_of_directed {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (D : I ⥤ GoodLift A F) : HasColimit D := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨ub, s, hsl, hcoc, hmax, hphi, hiota, hexh, huniv⟩ :=
    goodLift_colimit_chosen_noflat (fun i => D.obj i)
      (fun i j hij => (D.map (homOfLE hij)).ψ)
      (fun i => by rw [show homOfLE (le_refl i) = 𝟙 i from rfl, D.map_id]; rfl)
      (fun i j k hij hjk => by
        rw [show homOfLE (le_trans hij hjk) = homOfLE hij ≫ homOfLE hjk from rfl, D.map_comp]
        rfl)
      (fun i j hij => (D.map (homOfLE hij)).isLocal)
      (fun i j hij => (D.map (homOfLE hij)).φcomp)
      (fun i j hij => (D.map (homOfLE hij)).ιcomp)
  let leg (i : I) : Hom (D.obj i) ub :=
    { ψ := s i, isLocal := hsl i, maxeq := hmax i, φcomp := hphi i, ιcomp := hiota i }
  let cc : Cocone D :=
    { pt := ub
      ι :=
        { app := leg
          naturality := fun i j f => Hom.ext' (by
            change (s j).comp ((D.map f).ψ) = (RingHom.id ub.carrier).comp (s i)
            rw [RingHom.id_comp]
            exact hcoc i j (leOfHom f)) } }
  have key : ∀ sc : Cocone D, ∃ m : Hom ub sc.pt, ∀ i, m.ψ.comp (s i) = (sc.ι.app i).ψ := by
    intro sc
    obtain ⟨ψ, hψ⟩ := huniv sc.pt.carrier (fun i => (sc.ι.app i).ψ)
      (fun i j hij => congrArg Hom.ψ (sc.w (homOfLE hij)))
    exact ⟨Hom.ofExhaustive leg (fun i => sc.ι.app i) ψ hψ hexh i₀, hψ⟩
  exact ⟨⟨cc,
    { desc := fun sc => (key sc).choose
      fac := fun sc i => Hom.ext' ((key sc).choose_spec i)
      uniq := fun sc m hm => Hom.ext' (RingHom.ext fun z => by
        obtain ⟨i, x, rfl⟩ := hexh z
        exact DFunLike.congr_fun
          ((congrArg Hom.ψ (hm i)).trans ((key sc).choose_spec i).symm) x) }⟩⟩

/-- Good lifts admit the colimits needed to iterate a successor structure over a well-ordered
type: colimits of the shapes `Set.Iio j` for a successor limit `j`, and of the shape `J`. -/
private theorem hasIterationOfShape (J : Type w) [LinearOrder J] [OrderBot J] :
    HasIterationOfShape J (GoodLift A F) := by
  have : Nonempty J := ⟨⊥⟩
  constructor
  · intro j hj
    have : Nonempty (Set.Iio j) := ⟨⟨_, (not_isMin_iff.mp hj.not_isMin).choose_spec⟩⟩
    exact ⟨fun D => hasColimit_of_directed D⟩
  · exact ⟨fun D => hasColimit_of_directed D⟩

/-- **One monogenic step, as a successor.** Every good lift admits a morphism to a good lift
which, unless its residue embedding was already onto `F`, cuts out a strictly larger subfield of
`F`: adjoin an element of `F` outside the range (`goodLift_monogenic_step`). -/
private theorem exists_step (g : GoodLift A F) :
    ∃ (h : GoodLift A F) (_ : Hom g h),
      ¬ Function.Surjective g.ι → Set.range g.ι ⊂ Set.range h.ι := by
  classical
  by_cases hs : Function.Surjective g.ι
  · exact ⟨g, 𝟙 g, fun h => absurd hs h⟩
  · obtain ⟨α, hα⟩ : ∃ α : F, α ∉ Set.range g.ι :=
      (Set.ne_univ_iff_exists_notMem _).1 fun he => hs (Set.range_eq_univ.1 he)
    obtain ⟨h, m, hm, -, mmax, mφ, mι, hcov⟩ := goodLift_monogenic_step g α
    let f : Hom g h := { ψ := m, isLocal := hm, maxeq := mmax, φcomp := mφ, ιcomp := mι }
    exact ⟨h, f, fun _ => (Set.ssubset_iff_of_subset (range_ι_subset f)).2 ⟨α, hcov, hα⟩⟩

/-- The successor structure on good lifts: adjoin one missing element of `F` at each step,
starting from `A` itself. -/
private noncomputable def succStruct : SuccStruct (GoodLift A F) where
  X₀ := goodLift_trivial A F
  succ g := (exists_step g).choose
  toSucc g := (exists_step g).choose_spec.choose

/-- **The transfinite assembly.** For a local ring `A` and a field extension `F` of its residue
field there is a good lift of `A` towards `F` whose residue embedding is onto `F`, i.e. a flat
local `A`-algebra `A'` with `𝔪_{A'} = 𝔪_A A'` and residue field `F`.

This is the content of Stacks 03C3: starting from `goodLift_trivial` one adjoins the elements
of `F` one at a time by `exists_step` (i.e. `goodLift_monogenic_step`), taking the colimits of
`hasColimit_of_directed` at limit stages; the tower is the iteration of `succStruct` over an
index type longer than `Set F`, so some stage's residue embedding is already onto. -/
private theorem exists_surjective_ι :
    ∃ g : GoodLift A F, Function.Surjective g.ι := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  set κ : Cardinal.{w} := Order.succ (2 ^ Cardinal.mk F)
  have hne : Nonempty κ.ord.ToType := by
    rw [Ordinal.nonempty_toType_iff]
    simpa [Cardinal.ord_eq_zero] using (lt_of_le_of_lt zero_le (Order.lt_succ _)).ne'
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  have := hasIterationOfShape (A := A) (F := F) κ.ord.ToType
  set Φ := succStruct (A := A) (F := F)
  have hmono : StrictMono fun j => Set.range ((Φ.iterationFunctor κ.ord.ToType).obj j).ι := by
    intro j j' hjj'
    have hlt : Set.range ((Φ.iterationFunctor κ.ord.ToType).obj j).ι
        ⊂ Set.range ((Φ.iterationFunctor κ.ord.ToType).obj (Order.succ j)).ι := by
      rw [range_ι_eq_of_iso (Φ.iterationFunctorObjSuccIso j (not_isMax_iff.mpr ⟨j', hjj'⟩))]
      exact (exists_step _).choose_spec.choose_spec (hcon _)
    exact lt_of_lt_of_le hlt (range_ι_subset
      ((Φ.iterationFunctor κ.ord.ToType).map (homOfLE (Order.succ_le_of_lt hjj'))))
  have h1 : Cardinal.mk κ.ord.ToType ≤ Cardinal.mk (Set F) :=
    Cardinal.mk_le_of_injective hmono.injective
  rw [Cardinal.mk_ord_toType, Cardinal.mk_set] at h1
  exact absurd h1 (not_le.mpr (Order.lt_succ _))

end Assembly

end GoodLift

/-- **A residue field extension is realized by a flat local ring map**, in one universe and in
ring-map form: for a local ring `A` and a ring map `kmap : ResidueField A →+* F` into a field
there is a flat local `A`-algebra `A'` with `𝔪_{A'} = 𝔪_A A'` whose residue field is
`F`-isomorphic over `kmap`. -/
private theorem exists_flat_of_residueFieldHom (A : Type w) [CommRing A] [IsLocalRing A]
    (F : Type w) [Field F] (kmap : ResidueField A →+* F) :
    ∃ (A' : Type w) (_ : CommRing A') (_ : IsLocalRing A') (φ : A →+* A') (hφ : IsLocalHom φ),
      φ.Flat ∧ maximalIdeal A' = Ideal.map φ (maximalIdeal A) ∧
      ∃ σ : ResidueField A' ≃+* F,
        (σ : ResidueField A' →+* F).comp (@ResidueField.map A A' _ _ _ _ φ hφ) = kmap := by
  let : Algebra (ResidueField A) F := kmap.toAlgebra
  obtain ⟨g, hsurj⟩ := GoodLift.exists_surjective_ι (A := A) (F := F)
  exact ⟨g.carrier, g.commRing, g.isLocalRing, g.φ, g.hφ, g.flat, g.maxeq,
    RingEquiv.ofBijective g.ι ⟨g.ι.injective, hsurj⟩,
    g.hι.trans (RingHom.algebraMap_toAlgebra kmap)⟩

/-- The residue field map of a ring isomorphism of local rings cancels that of its inverse. -/
private theorem residueField_map_comp_map_symm {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (e : A ≃+* B) :
    (ResidueField.map (e : A →+* B)).comp (ResidueField.map (e.symm : B →+* A))
      = RingHom.id (ResidueField B) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := residue_surjective (R := B) x
  simp [ResidueField.map_residue]

/-- **The same across universes.** `exists_flat_of_residueFieldHom` for a local ring `A` and a
field `F` in independent universes, the algebra `A'` landing in `Type (max u v)`: run the
construction over `ULift.{v} A` and `ULift.{u} F` and transport the conclusion back along
`ULift.ringEquiv`, flatness by `RingHom.Flat.comp_iff_of_bijective_right`, the maximal ideal by
`IsLocalRing.map_ringEquiv_maximalIdeal` and the residue embedding by the cancellation
`residueField_map_comp_map_symm`. -/
private theorem exists_flat_of_residueFieldHom' (A : Type u) [CommRing A] [IsLocalRing A]
    (F : Type v) [Field F] (kmap : ResidueField A →+* F) :
    ∃ (A' : Type max u v) (_ : CommRing A') (_ : IsLocalRing A') (φ : A →+* A')
      (hφ : IsLocalHom φ),
      φ.Flat ∧ maximalIdeal A' = Ideal.map φ (maximalIdeal A) ∧
      ∃ σ : ResidueField A' ≃+* F,
        (σ : ResidueField A' →+* F).comp (@ResidueField.map A A' _ _ _ _ φ hφ) = kmap := by
  let e : ULift.{v} A ≃+* A := ULift.ringEquiv
  let f : ULift.{u} F ≃+* F := ULift.ringEquiv
  have : IsLocalRing (ULift.{v} A) := e.symm.isLocalRing
  obtain ⟨A', cA', lA', φ, hφ, hflat, hmax, σ, hσ⟩ :=
    exists_flat_of_residueFieldHom (ULift.{v} A) (ULift.{u} F)
      ((f.symm : F →+* ULift.{u} F).comp
        (kmap.comp (ResidueField.map (e : ULift.{v} A →+* A))))
  have := hφ
  refine ⟨A', cA', lA', φ.comp (e.symm : A →+* ULift.{v} A), inferInstance,
    (RingHom.Flat.comp_iff_of_bijective_right e.symm.bijective).2 hflat, ?_, σ.trans f, ?_⟩
  · rw [← Ideal.map_map, show Ideal.map (e.symm : A →+* ULift.{v} A) (maximalIdeal A)
      = maximalIdeal (ULift.{v} A) from map_ringEquiv_maximalIdeal e.symm]
    exact hmax
  · refine RingHom.ext fun x => ?_
    have h := DFunLike.congr_fun hσ (ResidueField.map (e.symm : A →+* ULift.{v} A) x)
    have hc := DFunLike.congr_fun (residueField_map_comp_map_symm e) x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      RingEquiv.coe_toRingHom] at h hc
    simp only [RingEquiv.coe_trans, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
      ResidueField.map_comp, h, RingEquiv.apply_symm_apply, hc]

/-- **A residue field extension is realized by a flat local ring map** (Stacks 03C3). Let
`(R, 𝔪, k)` be a local ring and let `K` be a field extension of `k`. Then there is a local ring
`(R', 𝔪', k')` and a local ring map `R → R'` such that `R'` is flat over `R`, `𝔪' = 𝔪 R'`, and
`k'` is isomorphic to `K` as an extension of `k`. -/
@[stacks 03C3 "The lemma's preamble, a local ring `R'` and a local ring map `R → R'`, is the
`Algebra R R'`, `IsLocalRing R'` and `IsLocalHom (algebraMap R R')` binders; the conjuncts are
flatness, `𝔪' = 𝔪 R'` as `Ideal.map`, and `k' ≅ K` as an extension of `k` as an
`≃ₐ[ResidueField R]`. `K` is allowed to live in a universe of its own, the source's case being
`v = u`. See the module docstring."]
theorem IsLocalRing.exists_flat_residueField_algEquiv (R : Type u) [CommRing R]
    [IsLocalRing R] (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R') (_ : IsLocalRing R')
      (_ : IsLocalHom (algebraMap R R')),
      Module.Flat R R' ∧
      (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' ∧
      Nonempty (ResidueField R' ≃ₐ[ResidueField R] K) := by
  obtain ⟨R', cR', lR', φ, hφ, hflat, hmax, σ, hσ⟩ :=
    exists_flat_of_residueFieldHom' R K (algebraMap (ResidueField R) K)
  have := hφ
  let : Algebra R R' := φ.toAlgebra
  have hAM : algebraMap R R' = φ := RingHom.algebraMap_toAlgebra φ
  have hlh : IsLocalHom (algebraMap R R') := hAM ▸ hφ
  refine ⟨R', cR', ‹Algebra R R'›, lR', hlh, ?_, by rw [hAM, hmax],
    ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => ?_⟩⟩
  · exact hflat
  · exact DFunLike.congr_fun hσ x

end
