import Langlands.Correspondence.Laumon.FieldMonodromy
import Langlands.Correspondence.Laumon.Completion
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Tame covers of the punctured line

Laumon (1987), (2.2.2), pp. 156–157, compares the Galois group of the punctured henselian trait
at an end of `𝔾_m = ℙ¹ - {0, ∞}` with the fundamental group of `𝔾_m` and its quotients classifying
the covers tamely ramified at one or both ends. This module constructs `𝔾_m` as the basic open
`x ≠ 0` of the affine line, the maps of the punctured end traits to it, the homomorphisms from
the local Galois groups to the étale fundamental group of `𝔾_m` at the image of the geometric
generic point of an end, the tame closure of the end field and tameness at an end for finite
étale covers and lisse sheaves. It states that the Kummer covers `u ^ n = x`, `p ∤ n`, are the
connected geometric covers tame at both ends (Laumon (1.1.3.7), Katz 1986, (1.2)–(1.3)), and that
restriction to an end identifies the tame fundamental group of `𝔾_m` with the tame quotient of
the local Galois group, arithmetically and geometrically (Laumon, Lemme (2.2.2.1)).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.Henniart.Laumon

section Gm

variable (k : Type u) [Field k]

/-- The punctured line `𝔾_m = Spec k[x, x⁻¹]`, as the basic open `x ≠ 0` of the affine line. -/
def gmOpen : (affineLine k).Opens := (affineLine k).basicOpen (lineCoordinate k)

/-- The structure morphism `𝔾_m → Spec k`. -/
def gmStructure : (gmOpen k : Scheme.{u}) ⟶ Spec (.of k) :=
  (gmOpen k).ι ≫ (affineLine k ↘ Spec (.of k))

/-- The coordinate `x` restricted to `𝔾_m`. -/
def gmCoordinate : Γ(gmOpen k, ⊤) := (gmOpen k).ι.appTop (lineCoordinate k)

/-- The coordinate is a unit on `𝔾_m`. -/
theorem gmCoordinate_isUnit : IsUnit (gmCoordinate k) := by
  have h : (gmOpen k : Scheme.{u}).basicOpen (gmCoordinate k) = ⊤ := by
    rw [gmCoordinate, ← Scheme.preimage_basicOpen_top]
    exact (gmOpen k).ι_preimage_self
  exact Scheme.isUnit_of_basicOpen_eq_top _ h

/-- The constants `k → Γ(𝔾_m, 𝒪)`. -/
def gmConstantHom : k →+* Γ(gmOpen k, ⊤) :=
  (gmStructure k).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- An integer `n` prime to the characteristic is invertible on `𝔾_m`. -/
theorem gmNatCast_isUnit {n : ℕ} (hn : ¬ ringChar k ∣ n) : IsUnit (n : Γ(gmOpen k, ⊤)) := by
  have h : (n : k) ≠ 0 := fun h => hn ((CharP.cast_eq_zero_iff k (ringChar k) n).mp h)
  rw [← map_natCast (gmConstantHom k)]
  exact (IsUnit.mk0 _ h).map _

/-- The Kummer cover `u ^ n = x` of `𝔾_m`, for `n ≥ 1` prime to the characteristic: the
finite étale cover of `n`-th roots of the coordinate, weil-conjectures's `kummerFiniteEtale`. -/
def gmKummerCover (n : ℕ) [NeZero n] (hn : ¬ ringChar k ∣ n) : (gmOpen k : Scheme.{u}).FiniteEtale :=
  Scheme.kummerFiniteEtale (Y := gmOpen k) (n := n) (f := gmCoordinate k) (gmNatCast_isUnit k hn)
    (gmCoordinate_isUnit k)

/-- The image of the punctured end trait in the affine line lies in `𝔾_m`: the coordinate pulls
back to the unit `t ^ ε` of the end field. -/
theorem range_puncturedEndToLine_subset (e : FourierEnd) :
    Set.range (puncturedEndToLine k e) ⊆ Set.range (gmOpen k).ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι, puncturedEndToLine, Scheme.Hom.comp_apply, SetLike.mem_coe, gmOpen]
  refine (affineLine.isoSpecPolynomial_inv_mem_basicOpen_iff k _).mpr ?_
  rw [Spec.map_apply]
  intro hX
  have hz := z.isPrime
  change X ∈ Ideal.comap _ z.asIdeal at hX
  rw [Ideal.mem_comap, CommRingCat.hom_ofHom, coe_eval₂RingHom, eval₂_X,
    Ideal.eq_bot_of_prime z.asIdeal, Ideal.mem_bot] at hX
  refine zpow_ne_zero _ ?_ hX
  intro h
  exact RatFunc.X_ne_zero ((map_eq_zero_iff _ (algebraMap (RatFunc k) (endField k)).injective).mp h)

/-- The map of the punctured end trait at `e` to `𝔾_m`: the lift of `puncturedEndToLine k e`
through the open immersion `𝔾_m → 𝔸¹`. -/
def puncturedEndToGm (e : FourierEnd) : puncturedEnd k e ⟶ gmOpen k :=
  IsOpenImmersion.lift (gmOpen k).ι (puncturedEndToLine k e) (range_puncturedEndToLine_subset k e)

/-- `𝔾_m` is affine, as a basic open of the affine scheme `𝔸¹_k`. -/
instance gmOpen_isAffine : IsAffine (gmOpen k : Scheme.{u}) := by
  unfold gmOpen
  infer_instance

/-- `𝔾_m` is smooth over `k`, as an open subscheme of `𝔸¹_k`. -/
instance gmStructure_smooth : Smooth (gmStructure k) := by
  unfold gmStructure
  infer_instance

/-- `𝔾_m` is locally Noetherian, being of finite type over `k`. -/
instance gmOpen_isLocallyNoetherian : IsLocallyNoetherian (gmOpen k : Scheme.{u}) :=
  LocallyOfFiniteType.isLocallyNoetherian (gmStructure k)

/-- `𝔾_m` is regular, being smooth over `k`. -/
instance gmOpen_isRegular : IsRegular (gmOpen k : Scheme.{u}) :=
  IsRegular.of_smooth (gmStructure k)

/-- `𝔾_m` is nonempty: it contains the image of a punctured end trait. -/
instance gmOpen_nonempty : Nonempty (gmOpen k) :=
  ⟨puncturedEndToGm k .zero (Classical.arbitrary _)⟩

/-- `𝔾_m` is integral, as a nonempty open of the integral scheme `𝔸¹_k`. -/
instance gmOpen_isIntegral : IsIntegral (gmOpen k : Scheme.{u}) := inferInstance

/-- The opposite end: `0 ↔ ∞` and `0' ↔ ∞'`. -/
def FourierEnd.opposite : FourierEnd → FourierEnd
  | .zero => .infinity
  | .infinity => .zero
  | .dualZero => .dualInfinity
  | .dualInfinity => .dualZero

/-- The geometric point of `𝔾_m` at the end `e`: the geometric generic point
`Spec Ω̄ → Spec Ω → η_e` of the end trait followed by `η_e → 𝔾_m`, with `Ω = endGenericClosure k`
and `Ω̄` its algebraic closure. -/
abbrev gmEndPoint (e : FourierEnd) :
    Spec (.of (AlgebraicClosure (endGenericClosure k))) ⟶ gmOpen k :=
  fieldGeometricPoint (endField k) (endGenericClosure k) ≫ puncturedEndToGm k e

/-- The local monodromy homomorphism at the end `e`: the Galois group of the end field acts on
the finite étale fibre functor of `η_e` (`fieldGaloisToAut`), and base change along
`η_e → 𝔾_m` (weil-conjectures's `pullbackPathHom`) gives the map `π₁(η_e) → π₁(𝔾_m)` at the
point `gmEndPoint k e`. -/
def gmLocalMonodromy (e : FourierEnd) :
    Gal(endGenericClosure k/endField k) →*
      Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e)) :=
  (Scheme.FiniteEtale.pullbackPathHom (puncturedEndToGm k e)
    (fieldGeometricPoint (endField k) (endGenericClosure k))).comp
    (fieldGaloisToAut (endField k) (endGenericClosure k))

/-- The geometric fundamental group `π₁(𝔾_m ⊗ k̄)` inside `π₁(𝔾_m)` at a geometric point `t`:
the kernel of the map to `π₁(Spec k)` induced by the structure morphism. -/
def gmGeometricSubgroup {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ gmOpen k) :
    Subgroup (Aut (Scheme.FiniteEtale.fiber t)) :=
  (Scheme.FiniteEtale.pullbackPathHom (gmStructure k) t).ker

end Gm

section Tame

variable (k : Type u) [Field k]

/-- The tame closure of the end field inside its separable generic closure: the field generated
by the constants `endConstants k` and the `N`-th roots of the uniformizer `t` for all `N ≥ 1`
prime to the characteristic. -/
def endTameField : IntermediateField (endField k) (endGenericClosure k) :=
  IntermediateField.adjoin (endField k)
    ((endConstants k : Set (endGenericClosure k)) ∪
      {ϖ | ∃ N : ℕ, 0 < N ∧ ¬ ringChar k ∣ N ∧
        ϖ ^ N = algebraMap (endField k) (endGenericClosure k)
          ((endUniformizer k .zero : endRing k) : endField k)})

/-- The wild inertia of the end field: the automorphisms fixing the tame closure. -/
def endWildInertia : Subgroup Gal(endGenericClosure k/endField k) :=
  (endTameField k).fixingSubgroup

/-- The finite étale cover `E` of `𝔾_m` is tame at the end `e`: the wild inertia of the end field
acts trivially on the fibre of `E` at `gmEndPoint k e`, through `gmLocalMonodromy k e`. -/
def IsTameCoverAt (e : FourierEnd) (E : (gmOpen k : Scheme.{u}).FiniteEtale) : Prop :=
  ∀ σ ∈ endWildInertia k, ∀ x : (Scheme.FiniteEtale.fiber (gmEndPoint k e)).obj E,
    gmLocalMonodromy k e σ • x = x

/-- The lisse sheaf `F` on `𝔾_m` is tame at the end `e`: the wild inertia of the end field acts
trivially on the monodromy of the pullback of `F` to the punctured end trait. -/
def IsTameLisseAt (ℓ : ℕ) [Fact ℓ.Prime] (e : FourierEnd) (F : ProEtale.LisseSheaf ℓ (gmOpen k)) :
    Prop :=
  ∀ σ ∈ endWildInertia k, ∀ v,
    fieldMonodromy ℓ (endField k) (endGenericClosure k) (F.upperStar ℓ (puncturedEndToGm k e)) σ v = v

end Tame

section Kernel

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The common kernel of the actions of `π₁(Y, t) = Aut (fiber t)` on the fibres at `t` of the
finite étale covers with a property `P`: the automorphisms acting trivially on all these fibres.
When the covers with `P` form a full Galois subcategory of the finite étale covers of a connected
`Y` (for instance the covers tame at given ends), the quotient by this kernel classifies exactly
the covers with `P`. -/
def coverKernel (t : Spec (.of Ω) ⟶ Y) (P : ObjectProperty Y.FiniteEtale) :
    Subgroup (Aut (Scheme.FiniteEtale.fiber t)) where
  carrier := {g | ∀ E, P E → ∀ x : (Scheme.FiniteEtale.fiber t).obj E, g • x = x}
  one_mem' _ _ x := one_smul _ x
  mul_mem' {g h} hg hh E hE x := by rw [mul_smul, hh E hE, hg E hE]
  inv_mem' {g} hg E hE x := by
    conv_lhs => rw [← hg E hE x]
    rw [inv_smul_smul]

end Kernel

/-- **Geometric cofinality of the Kummer covers** (Laumon, Remarque (1.1.3.7), p. 140, and Lemme
(2.2.2.1), p. 157; Katz 1986, (1.1.1), p. 71, for the power maps and (1.3.2), p. 75, for their
use with exponents prime to `p`). For an algebraically closed field `κ`, the Kummer
cover `u ^ n = x` of `𝔾_m` is connected and tame at `0` and `∞` for every `n ≥ 1` prime to the
characteristic, and every connected finite étale cover of `𝔾_m` tame at `0` and at `∞` is
isomorphic to one of them. -/
def GeometricTameKummerCofinalityStatement : Prop :=
  ∀ (κ : Type u) [Field κ] [IsAlgClosed κ],
    (∀ (n : ℕ) [NeZero n] (hn : ¬ ringChar κ ∣ n),
      PreGaloisCategory.IsConnected (gmKummerCover κ n hn) ∧
        IsTameCoverAt κ .zero (gmKummerCover κ n hn) ∧
        IsTameCoverAt κ .infinity (gmKummerCover κ n hn)) ∧
    ∀ E : (gmOpen κ : Scheme.{u}).FiniteEtale, PreGaloisCategory.IsConnected E →
      IsTameCoverAt κ .zero E → IsTameCoverAt κ .infinity E →
        ∃ (n : ℕ) (_ : NeZero n) (hn : ¬ ringChar κ ∣ n), Nonempty (gmKummerCover κ n hn ≅ E)

/-- **The tame comparison at an end** (Laumon, Lemme (2.2.2.1), p. 157). For a finite field `k`
and an end `e`, let `ρ = gmLocalMonodromy k e` and let `N` be the kernel of the action of
`π₁(𝔾_m)` on the covers tame at `0` and at `∞`. Then `ρ⁻¹(N)` is the wild inertia and every
element of `π₁(𝔾_m)` is `ρ(σ)` modulo `N`, so `ρ` induces an isomorphism from the tame quotient
of the Galois group of the end field onto the tame fundamental group of `𝔾_m`. Geometrically,
`ρ` maps the inertia group (the automorphisms fixing `endUnramifiedField k`) into the geometric
fundamental group, and every geometric element is `ρ(σ)` modulo `N` for an inertia element `σ`. -/
def TamePuncturedLineEquivalenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (e : FourierEnd),
    (∀ σ : Gal(endGenericClosure k/endField k),
      gmLocalMonodromy k e σ ∈ coverKernel (gmEndPoint k e)
          (fun E => IsTameCoverAt k .zero E ∧ IsTameCoverAt k .infinity E) ↔
        σ ∈ endWildInertia k) ∧
    (∀ g : Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e)), ∃ σ,
      g⁻¹ * gmLocalMonodromy k e σ ∈ coverKernel (gmEndPoint k e)
        (fun E => IsTameCoverAt k .zero E ∧ IsTameCoverAt k .infinity E)) ∧
    (∀ σ ∈ (endUnramifiedField k).fixingSubgroup,
      gmLocalMonodromy k e σ ∈ gmGeometricSubgroup k (gmEndPoint k e)) ∧
    ∀ g ∈ gmGeometricSubgroup k (gmEndPoint k e), ∃ σ ∈ (endUnramifiedField k).fixingSubgroup,
      g⁻¹ * gmLocalMonodromy k e σ ∈ coverKernel (gmEndPoint k e)
        (fun E => IsTameCoverAt k .zero E ∧ IsTameCoverAt k .infinity E)

end Langlands.Henniart.Laumon
