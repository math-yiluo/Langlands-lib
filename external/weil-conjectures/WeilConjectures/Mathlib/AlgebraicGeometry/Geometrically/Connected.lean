/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Geometrically connected schemes

## Main statements

- `AlgebraicGeometry.GeometricallyConnected.of_geometricallyIrreducible`: a geometrically
  irreducible morphism is geometrically connected.
- `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_isSepClosed`,
  `AlgebraicGeometry.GeometricallyConnected.of_isSepClosed`: a connected scheme over a
  separably closed field is geometrically connected.
- `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_section`: a connected scheme
  over a field with a rational point is geometrically connected.
- `AlgebraicGeometry.GeometricallyConnected.of_isOpenImmersion`: an irreducible scheme over a
  field with a nonempty geometrically connected open subscheme is geometrically connected.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A geometrically irreducible morphism is geometrically connected, since an irreducible space
is connected. -/
instance (priority := low) GeometricallyConnected.of_geometricallyIrreducible
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] : GeometricallyConnected f where
  geometrically_connectedSpace _ _ y _ fst snd h :=
    have := GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd h
    inferInstance

/-- Over a separably closed field `k`, the spectrum of a field extension `L` of `k` is
geometrically connected: for every field `K` over `k` the ring `L ⊗[k] K` has no nontrivial
idempotents (`IsSepClosed.eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct`). -/
theorem GeometricallyConnected.SpecMap_algebraMap_of_isSepClosed (k L : Type u) [Field k]
    [IsSepClosed k] [Field L] [Algebra k L] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ ↦ ?_⟩
  refine (pullbackSpecIso k L K).hom.homeomorph.connectedSpace_iff.mpr ?_
  exact PrimeSpectrum.connectedSpace_of_isIdempotentElem _ fun e he ↦
    IsSepClosed.eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct
      (fun a ha ↦ IsIdempotentElem.iff_eq_zero_or_one.mp ha) he

/-- A connected scheme over a separably closed field `k` is geometrically connected over `k`
(Stacks 0363): for a field `K` over `k`, the base change `X_K` is the product of the connected
scheme `X` with the geometrically connected `Spec K`, along a universally open morphism. -/
@[stacks 0363]
theorem GeometricallyConnected.of_connectedSpace_of_isSepClosed {k : Type u} [Field k]
    [IsSepClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  have := SpecMap_algebraMap_of_isSepClosed k K
  exact (inferInstance : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom
    (algebraMap k K)))))

/-- A connected scheme over a separably closed field `k` is geometrically connected over `k`. -/
theorem GeometricallyConnected.of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [ConnectedSpace X] :
    GeometricallyConnected (X ↘ Spec (.of k)) :=
  of_connectedSpace_of_isSepClosed _

/-- Let `X` be a connected scheme over a field `k` with a `k`-rational point, that is, a section
`s` of its structure morphism `f`. Then `X_K` is connected for every algebraic extension `K` of
`k`. Indeed, the projection `p : X_K ⟶ X` is integral, hence closed, and open, and its fibre over
the rational point is a single point. If `X_K` were the disjoint union of two nonempty clopen
subsets, their images under `p` would be nonempty clopen subsets of `X`, hence all of `X`, so
both would meet the fibre over the rational point. -/
theorem GeometricallyConnected.connectedSpace_pullback_of_section_of_isAlgebraic {k K : Type u}
    [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [ConnectedSpace X] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsIntegralHom g := by
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral
  set p := pullback.fst f g
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (.of k)))
  -- the fibre of `p` over the rational point `s t` has at most one point
  have hfib (z z' : ↥(pullback f g)) (hz : p z = s t) (hz' : p z' = s t) : z = z' := by
    obtain ⟨w, -, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := p) _ _ hz.symm
    obtain ⟨w', -, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := p) _ _
      hz'.symm
    let e := pullbackRightPullbackFstIso f g s ≪≫ pullback.congrHom hs rfl ≪≫
      asIso (pullback.snd (𝟙 _) g)
    have : Subsingleton ↥(pullback s p) := e.hom.homeomorph.subsingleton_congr.mpr inferInstance
    rw [Subsingleton.elim w w']
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨pullback.lift (g ≫ s) (𝟙 _) (by simp [hs]) (Nonempty.some inferInstance)⟩,
    fun T hT ↦ ?_⟩
  by_contra! hne
  obtain ⟨hT₁, hT₂⟩ := hne
  have himage (T : Set ↥(pullback f g)) (hT : IsClopen T) (hT' : T.Nonempty) :
      ∃ z ∈ T, p z = s t := by
    have hc : IsClopen (p '' T) := ⟨p.isClosedMap _ hT.isClosed, p.isOpenMap _ hT.isOpen⟩
    rcases isClopen_iff.mp hc with h | h
    · exact absurd h (hT'.image _).ne_empty
    · obtain ⟨z, hz, hzt⟩ : s t ∈ p '' T := h ▸ Set.mem_univ (s t)
      exact ⟨z, hz, hzt⟩
  obtain ⟨z, hz, hzt⟩ := himage T hT hT₁
  obtain ⟨z', hz', hzt'⟩ := himage Tᶜ hT.compl (Set.nonempty_compl.mpr hT₂)
  exact hz' (hfib z z' hzt hzt' ▸ hz)

/-- A connected scheme `X` over a field `k` with a `k`-rational point, that is, a section `s` of
its structure morphism `f`, is geometrically connected over `k`.

Let `K` be a field over `k`, let `Ω` be an algebraic closure of `K` and let `k̄ ⊆ Ω` be an
algebraic closure of `k`. The base change `X_k̄` is connected
(`connectedSpace_pullback_of_section_of_isAlgebraic`), hence geometrically connected over the
separably closed field `k̄` (`of_connectedSpace_of_isSepClosed`). So `X_Ω = (X_k̄)_Ω` is
connected, and it surjects onto `X_K`. -/
@[stacks 04KV]
theorem GeometricallyConnected.of_connectedSpace_of_section {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [ConnectedSpace X] (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  change ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  let Ω := AlgebraicClosure K
  let kb := AlgebraicClosure k
  let ι : kb →ₐ[k] Ω := IsAlgClosed.lift
  algebraize [ι.toRingHom]
  have : IsScalarTower k kb Ω := .of_algHom ι
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let gkb := Spec.map (CommRingCat.ofHom (algebraMap k kb))
  let gΩK := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let gΩkb := Spec.map (CommRingCat.ofHom (algebraMap kb Ω))
  have : ConnectedSpace ↥(pullback f gkb) :=
    connectedSpace_pullback_of_section_of_isAlgebraic f s hs
  have : GeometricallyConnected (pullback.snd f gkb) :=
    of_connectedSpace_of_isSepClosed _
  have : ConnectedSpace ↥(pullback (pullback.snd f gkb) gΩkb) :=
    pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace _ _
  have heq : gΩkb ≫ gkb = gΩK ≫ gK := by
    simp only [gΩkb, gkb, gΩK, gK, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  let e := pullbackLeftPullbackSndIso f gkb gΩkb ≪≫ pullback.congrHom rfl heq ≪≫
    (pullbackLeftPullbackSndIso f gK gΩK).symm
  have : ConnectedSpace ↥(pullback (pullback.snd f gK) gΩK) :=
    e.hom.homeomorph.connectedSpace_iff.mp inferInstance
  have : Surjective gΩK := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst (pullback.snd f gK) gΩK).surjective.connectedSpace
    (pullback.fst (pullback.snd f gK) gΩK).continuous

/-- An irreducible scheme `Y` over a field `K` containing a nonempty open subscheme `X` which is
geometrically connected over `K` is geometrically connected over `K`. After a base change to a
field `L`, the open `X_L` is connected, and it is dense in `Y_L`: the projection `Y_L ⟶ Y` is
flat, hence generalizing, so every point of `Y_L` specializes from a point over the generic point
of `Y`, which lies in `X`. A space with a dense connected subset is connected. -/
theorem GeometricallyConnected.of_isOpenImmersion {K : Type u} [Field K] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] [Nonempty X] [IrreducibleSpace Y] (f : Y ⟶ Spec (.of K))
    [GeometricallyConnected (j ≫ f)] : GeometricallyConnected f where
  geometrically_connectedSpace L _ y Z fst snd h := by
    have hW : IsPullback (pullback.fst j fst) (pullback.snd j fst ≫ snd) (j ≫ f) y :=
      (IsPullback.of_hasPullback j fst).paste_vert h
    have : ConnectedSpace ↥(pullback j fst) :=
      GeometricallyConnected.geometrically_connectedSpace (f := j ≫ f) y _ _ hW
    have : Flat y := by
      rw [← Spec.map_preimage y, Flat.SpecMap_iff]
      algebraize [(Spec.preimage y).hom]
      exact (inferInstance : Module.Flat K L)
    have : Flat fst := MorphismProperty.of_isPullback h.flip ‹_›
    have hgen := Flat.generalizingMap fst
    have hη : genericPoint Y ∈ Set.range j.base := by
      obtain ⟨x⟩ := ‹Nonempty X›
      exact ((genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
        ⟨j.base x, trivial, x, rfl⟩
    have hdense : Dense (Set.range (pullback.snd j fst).base) := by
      refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun z ↦ ?_)
      obtain ⟨z', hz', hz'η⟩ := hgen (genericPoint_specializes (fst.base z))
      obtain ⟨x, hx⟩ := hη
      obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback x z' (hx.trans hz'η.symm)
      exact hz'.mem_closed (isClosed_closure) (subset_closure ⟨w, hw⟩)
    have hconn : _root_.IsConnected (Set.range (pullback.snd j fst).base) :=
      isConnected_range (pullback.snd j fst).base.hom.continuous
    have := hconn.closure
    rw [hdense.closure_eq] at this
    exact connectedSpace_iff_univ.mpr this

end AlgebraicGeometry
