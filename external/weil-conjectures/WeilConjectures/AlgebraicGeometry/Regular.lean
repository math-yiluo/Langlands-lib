/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.AlgebraicGeometry.NoetherianComponents
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Mathlib.RingTheory.Smooth.Local
public import WeilConjectures.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# Regular schemes

A scheme is *regular* if all of its local rings are regular local rings. Mathlib has the
predicate `IsRegularLocalRing` on commutative rings but no class for schemes, so it is
introduced here; it is a hypothesis of the divisor sequence and of Grothendieck's residue
injection for the Brauer group.

## Main statements

- `AlgebraicGeometry.isRegularLocalRing_stalk_of_etale`: a scheme étale over a regular scheme
  is regular.
- `AlgebraicGeometry.isRegularLocalRing_stalk_pullback`: a product of regular schemes locally
  of finite type over a perfect field is regular.
- `AlgebraicGeometry.IsRegular.of_smooth`: a scheme smooth over a field is regular.
- `AlgebraicGeometry.smooth_of_isRegular`: a regular scheme locally of finite type over a perfect
  field is smooth over it.
- `AlgebraicGeometry.IsRegular.of_isIntegrallyClosed_stalk`: a locally noetherian scheme of
  dimension at most one whose local rings are integrally closed domains is regular.
- `AlgebraicGeometry.isIntegrallyClosed_stalk_of_isRegular`: conversely, the local rings of a
  regular locally noetherian scheme of dimension at most one are integrally closed.
- `AlgebraicGeometry.IsRegular.irreducibleSpace`: a connected locally noetherian regular scheme
  is irreducible.
- `AlgebraicGeometry.GeometricallyIrreducible.of_smooth_of_geometricallyConnected`: a smooth
  morphism with geometrically connected fibres has geometrically irreducible fibres.
- `AlgebraicGeometry.IsRegular.isRegularRing_stalk`: the local rings of a regular scheme are
  regular rings, i.e. all their localizations at primes are regular local rings.
- `AlgebraicGeometry.IsRegular.uniqueFactorizationMonoid_stalk`: the local rings of a regular
  scheme are unique factorization domains.
- `AlgebraicGeometry.IsRegular.isIntegrallyClosed_stalk`: regular schemes are normal.
- `AlgebraicGeometry.IsRegular.exists_isClopen_isIntegral`: a Noetherian regular scheme is a
  finite disjoint union of open and closed normal integral subschemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme is *regular* if the local ring at each of its points is a regular local ring. -/
@[mk_iff]
class IsRegular (X : Scheme.{u}) : Prop where
  /-- The local ring of a regular scheme at any point is a regular local ring. -/
  isRegularLocalRing_stalk (x : X) : IsRegularLocalRing (X.presheaf.stalk x)

attribute [instance] IsRegular.isRegularLocalRing_stalk

/-- The spectrum of a field is regular: its local ring is the localization of the field at its
zero ideal. -/
instance IsRegular.spec_field (k : Type u) [Field k] : IsRegular (Spec (.of k)) :=
  ⟨fun z ↦ IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of k) z).commRingCatIsoToRingEquiv.symm⟩

/-- If the local rings of `X` at the points of an affine open `U` are regular local rings, then
so are the localizations of `Γ(X, U)` at primes: the localization at `p` is the local ring of `X`
at the point of `U` corresponding to `p`. -/
theorem IsAffineOpen.isRegularLocalRing_localization {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (hX : ∀ x ∈ U, IsRegularLocalRing (X.presheaf.stalk x))
    (p : Ideal Γ(X, U)) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) := by
  have hy : hU.fromSpec ⟨p, inferInstance⟩ ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self _
  let := X.presheaf.algebra_section_stalk ⟨_, hy⟩
  have := hU.isLocalization_stalk' ⟨p, inferInstance⟩ hy
  have := hX _ hy
  exact .of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (X.presheaf.stalk (hU.fromSpec ⟨p, inferInstance⟩)) (Localization.AtPrime p)).toRingEquiv

/-- A scheme étale over a regular scheme is regular: an étale local homomorphism of local rings
is flat with regular (indeed trivial) closed fibre, so it preserves regularity. -/
theorem isRegularLocalRing_stalk_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU)
      (f ⁻¹ᵁ U).isOpen
  have hφ := HasRingHomProperty.appLE @Etale f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  algebraize [(f.appLE U V hVU).hom]
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  set P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have := IsRegularLocalRing.localization_of_etale_of_comap (R := Γ(Y, U)) P
    (hU.isRegularLocalRing_localization (fun y _ ↦ hY y) _)
  exact .of_ringEquiv
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv

/-- A scheme smooth over a field `k` is regular: the local rings of a smooth `k`-scheme are
regular local rings, hence domains (`IsRegularLocalRing.isDomain`). Near any point `X` is étale
over an affine space `𝔸ⁿ_k`, whose local rings are regular, and étale maps preserve regularity.

(blueprint: `lem-sc-smooth-regular`) -/
theorem IsRegular.of_smooth {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] : IsRegular X :=
  ⟨Smooth.isRegularLocalRing_stalk f⟩

/-- A regular scheme locally of finite type over a perfect field `k` is smooth over `k`: at a
point `x` the residue field is finitely generated over the perfect field `k`, hence separably
generated, and a regular local `k`-algebra essentially of finite type with such a residue field
is smooth over `k` (Stacks `00TV`). This is the main input of
`AlgebraicGeometry.Scheme.smooth_fromNormalization_comp` (blueprint:
`lemma-proper-smooth-model--1`). -/
theorem smooth_of_isRegular {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsRegular X] : Smooth f := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Smooth) (fun V : X.affineOpens ↦ V)
    (iSup_affineOpens_eq_top X) fun V ↦ ?_
  set φ := (f.appLE ⊤ V le_top).hom
  have hφ : φ.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨⊤, isAffineOpen_top _⟩ V le_top
  set e := (Scheme.ΓSpecIso (.of k)).inv.hom
  set e' := (Scheme.ΓSpecIso (.of k)).hom.hom
  have he : e.comp e' = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
  have he' : Function.Bijective e' :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom)
  have hψ : (φ.comp e).Smooth := by
    have hft : (φ.comp e).FiniteType := hφ.comp (.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
    let := (φ.comp e).toAlgebra
    have : Algebra.FiniteType k Γ(X, V) := hft
    exact Algebra.Smooth.of_isRegularLocalRing (k := k)
      (V.2.isRegularLocalRing_localization fun x _ ↦ IsRegular.isRegularLocalRing_stalk x)
  have := RingHom.Smooth.comp (RingHom.Smooth.of_bijective he') hψ
  rwa [RingHom.comp_assoc, he, RingHom.comp_id] at this

/-- The product of two regular schemes locally of finite type over a perfect field `k` is
regular: over a perfect field such schemes are smooth, and smoothness is stable under base
change and composition. -/
theorem isRegularLocalRing_stalk_pullback {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (z : ↥(pullback f g)) :
    IsRegularLocalRing ((pullback f g).presheaf.stalk z) := by
  have : IsRegular X := ⟨hX⟩
  have : IsRegular Y := ⟨hY⟩
  have := smooth_of_isRegular f
  have := smooth_of_isRegular g
  exact (IsRegular.of_smooth (pullback.fst f g ≫ f)).isRegularLocalRing_stalk z

/-- A locally noetherian scheme of dimension at most one whose local rings are integrally closed
domains is regular: each local ring is a field or a discrete valuation ring.
(blueprint: `lemma-proper-smooth-model--1`) -/
theorem IsRegular.of_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X ≤ 1) : IsRegular X := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨_, _⟩ := hX x
  exact .of_isIntegrallyClosed _ ((ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim)

/-- **The normalized curve over a perfect field is smooth.** Let `X` be an integral scheme of
finite type and of dimension one over a perfect field `k`. Its normalization `X^ν` in the function
field is normal of dimension one, so its local rings are fields or discrete valuation rings; hence
`X^ν` is regular, and therefore smooth over `k` (`AlgebraicGeometry.smooth_of_isRegular`).
(blueprint: `lemma-proper-smooth-model--1`) -/
theorem Scheme.smooth_fromNormalization_comp {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hdim : topologicalKrullDim X = 1) : Smooth (X.fromNormalization ≫ q) := by
  have := X.isFinite_fromNormalization_of_locallyOfFiniteType q
  have : IsLocallyNoetherian X.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (X.fromNormalization ≫ q)
  -- the local rings of `Spec k(X)` are integrally closed
  have hK (x : Spec X.functionField) :
      IsIntegrallyClosed ((Spec X.functionField).presheaf.stalk x) := by
    let := TopCat.Presheaf.algebra_section_stalk (Spec X.functionField).presheaf
      (⟨x, trivial⟩ : (⊤ : (Spec X.functionField).Opens))
    have := (isAffineOpen_top (Spec X.functionField)).isLocalization_stalk ⟨x, trivial⟩
    have : IsIntegrallyClosed Γ(Spec X.functionField, ⊤) :=
      .of_equiv (Scheme.ΓSpecIso X.functionField).commRingCatIsoToRingEquiv.symm
    exact isIntegrallyClosed_of_isLocalization _ _
      ((isAffineOpen_top _).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
  have : IsRegular X.normalization := IsRegular.of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance, X.fromSpecFunctionField.isIntegrallyClosed_stalk_normalization hK y⟩)
    (X.topologicalKrullDim_normalization q ▸ hdim).le
  exact smooth_of_isRegular _

/-- **Properties of the normalization.** Let `X` be an integral scheme of finite type over a
field `k`, and `ν : X^ν ⟶ X` its normalization in the function field.

* **(a)** `ν` is finite and surjective, and `dim X^ν = dim X`; if `X` is proper over `k`, so is
  `X^ν`.
* **(b)** `ν` is an isomorphism over every open of `X` whose local rings are integrally closed.
* **(c)** If `dim X = 1` and `k` is perfect, then `X^ν` is smooth over `k`.
(blueprint: `lemma-proper-smooth-model--1`) -/
theorem Scheme.normalization_properties {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] :
    (IsFinite X.fromNormalization ∧ Surjective X.fromNormalization ∧
      topologicalKrullDim X.normalization = topologicalKrullDim X ∧
      (IsProper q → IsProper (X.fromNormalization ≫ q))) ∧
    (∀ U : X.Opens, (∀ x ∈ U, IsIntegrallyClosed (X.presheaf.stalk x)) →
      IsIso (X.fromNormalization ∣_ U)) ∧
    (PerfectField k → topologicalKrullDim X = 1 → Smooth (X.fromNormalization ≫ q)) := by
  have := X.isFinite_fromNormalization_of_locallyOfFiniteType q
  exact ⟨⟨this, inferInstance, X.topologicalKrullDim_normalization q, fun _ ↦ inferInstance⟩,
    fun U hU ↦ X.isIso_fromNormalization_restrict U hU,
    fun _ hdim ↦ Scheme.smooth_fromNormalization_comp q hdim⟩


/-- The local rings of a regular locally noetherian scheme of dimension at most one are
integrally closed: each of them is a field or a discrete valuation ring. -/
theorem isIntegrallyClosed_stalk_of_isRegular {X : Scheme.{u}} [IsRegular X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
  IsRegularLocalRing.isIntegrallyClosed _ ((ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim)

/-- **Smooth curves are normal.** The local rings of a scheme of dimension at most one which is
smooth over a field `k` are integrally closed: they are regular local rings
(`AlgebraicGeometry.IsRegular.of_smooth`) of dimension at most one, hence fields or discrete
valuation rings. (blueprint: `lemma-proper-smooth-model--1`) -/
theorem isIntegrallyClosed_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) :=
  have := IsRegular.of_smooth f
  isIntegrallyClosed_stalk_of_isRegular hdim x

/-- A connected locally noetherian regular scheme is irreducible, since its local rings, being
regular, are integral domains. This is the consequence recorded in blueprint
`rem-pc-regular-normal`; see also `AlgebraicGeometry.IsRegular.exists_isClopen_isIntegral`. -/
theorem IsRegular.irreducibleSpace (X : Scheme.{u}) [IsRegular X] [IsLocallyNoetherian X]
    [ConnectedSpace X] : IrreducibleSpace X :=
  irreducibleSpace_of_isDomain_stalk X fun _ ↦ inferInstance

/-- A nonempty connected locally noetherian regular scheme is integral: it is irreducible
(`AlgebraicGeometry.IsRegular.irreducibleSpace`), and reduced since its local rings are
integral domains. -/
theorem IsRegular.isIntegral (X : Scheme.{u}) [IsRegular X] [IsLocallyNoetherian X]
    [ConnectedSpace X] : IsIntegral X :=
  have := IsRegular.irreducibleSpace X
  have := isReduced_of_isReduced_stalk X
  isIntegral_of_irreducibleSpace_of_isReduced X

/-- A smooth morphism with geometrically connected fibres has geometrically irreducible fibres:
a base change of it to a field is smooth over that field, hence regular and locally noetherian,
and connected, hence irreducible. -/
theorem GeometricallyIrreducible.of_smooth_of_geometricallyConnected {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIrreducible f where
  geometrically_irreducibleSpace _ _ y _ fst snd h := by
    have := GeometricallyConnected.geometrically_connectedSpace y fst snd h
    have : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
    have := LocallyOfFiniteType.isLocallyNoetherian snd
    have := IsRegular.of_smooth snd
    exact IsRegular.irreducibleSpace _

/-- The local rings of a regular scheme are regular rings: the localization of `𝒪_{X,x}` at a
prime is the local ring of `X` at a generization of `x`. Concretely, if `U ∋ x` is an affine open,
then `𝒪_{X,x}` is a localization of `Γ(X, U)`, so its localization at a prime `q` is the
localization of `Γ(X, U)` at the prime `P` below `q`, which is the stalk at the point of `U`
corresponding to `P`. -/
theorem IsRegular.isRegularRing_stalk {X : Scheme.{u}} [IsRegular X] (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  rw [isRegularRing_iff]
  intro q _
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (Localization.AtPrime q) q
  let y : PrimeSpectrum Γ(X, U) :=
    ⟨q.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)), inferInstance⟩
  have hy : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self y
  let := X.presheaf.algebra_section_stalk ⟨hU.fromSpec y, hy⟩
  have := hU.isLocalization_stalk' y hy
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv y.asIdeal.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime q)).toRingEquiv

/-- **Auslander–Buchsbaum theorem** for schemes: the local rings of a regular scheme are unique
factorization domains. -/
theorem IsRegular.uniqueFactorizationMonoid_stalk {X : Scheme.{u}} [IsRegular X] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  have := isRegularRing_stalk x
  IsRegularLocalRing.uniqueFactorizationMonoid _

/-- **Regular schemes are normal** (Stacks 0569): the local rings of a regular scheme are
integrally closed domains. They are unique factorization domains
(`AlgebraicGeometry.IsRegular.uniqueFactorizationMonoid_stalk`), and a unique factorization
domain is integrally closed. -/
@[stacks 0569]
theorem IsRegular.isIntegrallyClosed_stalk {X : Scheme.{u}} [IsRegular X] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) :=
  have := uniqueFactorizationMonoid_stalk x
  inferInstance

/-- Blueprint `rem-pc-regular-normal`: Regular schemes are normal; the normal decomposition.

Regular schemes are normal (Stacks 0569, `AlgebraicGeometry.IsRegular.isIntegrallyClosed_stalk`)
and a Noetherian normal scheme is a finite disjoint union of normal integral schemes (Stacks
033M, `AlgebraicGeometry.Scheme.exists_isClopen_isIntegral_of_isIntegrallyClosed_stalk`). So a
Noetherian regular scheme `X` is a finite disjoint union of open and closed subschemes `X_a`,
each integral with integrally closed local rings. In particular a regular, connected, Noetherian
scheme is integral (`AlgebraicGeometry.IsRegular.isIntegral`), hence irreducible
(`AlgebraicGeometry.IsRegular.irreducibleSpace`). -/
theorem IsRegular.exists_isClopen_isIntegral (X : Scheme.{u}) [IsRegular X] [IsNoetherian X] :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ a, IsClopen (U a : Set X)) ∧
      Pairwise (fun a b ↦ Disjoint (U a) (U b)) ∧ ⨆ a, U a = ⊤ ∧
      ∀ a, IsIntegral (U a).toScheme ∧
        ∀ x : (U a).toScheme, IsIntegrallyClosed ((U a).toScheme.presheaf.stalk x) :=
  X.exists_isClopen_isIntegral_of_isIntegrallyClosed_stalk fun x ↦
    ⟨inferInstance, isIntegrallyClosed_stalk x⟩

end AlgebraicGeometry
