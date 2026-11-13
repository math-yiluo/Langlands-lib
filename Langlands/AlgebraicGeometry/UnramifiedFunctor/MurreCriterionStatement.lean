import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! # Murre's criterion for unramified functors (Bourbaki exp. 294, Theorem 1, Corollary 1) -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}}

section Algebras

variable {A : Type u} [CommRing A] (f : Spec (CommRingCat.of A) ⟶ S)

/-- For an `A`-algebra `B`, the affine scheme `Spec B` as an object of `Over S`, through
`Spec B ⟶ Spec A ⟶ S`. -/
abbrev algebraOver (B : Type u) [CommRing B] [Algebra A B] : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f)

/-- The structure morphism `Spec B ⟶ Spec A` as a morphism of `Over S`. -/
def algebraOverBase (B : Type u) [CommRing B] [Algebra A B] :
    algebraOver f B ⟶ Over.mk f :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- An `A`-algebra map `φ : B → C` as the morphism `Spec C ⟶ Spec B` of `Over S`. -/
def algHomOver {B C : Type u} [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
    (φ : B →ₐ[A] C) : algebraOver f C ⟶ algebraOver f B :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : B →+* C))) (by
    dsimp
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

/-- The functor `B ↦ Spec B` from commutative `A`-algebras to `(Over S)ᵒᵖ`. -/
def algebraFunctor : CommAlgCat.{u} A ⥤ (Over S)ᵒᵖ where
  obj B := op (algebraOver f B)
  map φ := (algHomOver f φ.hom).op
  map_id B := by
    apply Quiver.Hom.unop_inj
    ext1
    simp [algHomOver]
  map_comp φ ψ := by
    apply Quiver.Hom.unop_inj
    ext1
    simp [algHomOver]
    rw [← Spec.map_comp]
    rfl

end Algebras

variable (F : (Over S)ᵒᵖ ⥤ Type v)

/-- Murre's functors take values in sets of the universe of the test schemes: every value
of `F` is `u`-small. -/
def SmallValues : Prop :=
  ∀ T : Over S, Small.{u} (F.obj (op T))

/-- Condition (F1a): for every test object `T` and every Zariski open covering of `T`,
`F(T) → ∏ F(U_α) ⇉ ∏ F(U_α ×_T U_β)` is exact. -/
def ZariskiSheaf : Prop :=
  ∀ (T : Over S) (𝒰 : T.left.OpenCover.{u}),
    Presieve.IsSheafFor F
      (Presieve.ofArrows (fun i ↦ Over.mk (𝒰.f i ≫ T.hom))
        (fun i ↦ (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)))

/-- Condition (F1b): for every faithfully flat, quasi-compact morphism `T' ⟶ T` of test
objects, `F(T) → F(T') ⇉ F(T' ×_T T')` is exact. -/
def FaithfullyFlatSheaf : Prop :=
  ∀ ⦃T' T : Over S⦄ (g : T' ⟶ T), Flat g.left → Surjective g.left → QuasiCompact g.left →
    Presieve.IsSheafFor F (Presieve.singleton g)

/-- Condition (F2): for every affine open `Spec R ⟶ S`, the functor `B ↦ F(Spec B)` on
`R`-algebras sends filtered colimits to colimits, i.e. for a filtered system `A_α` of
`R`-algebras with colimit `A`, the map `colim F(Spec A_α) → F(Spec A)` is bijective. -/
def FilteredColimits : Prop :=
  ∀ (R : Type u) [CommRing R] (f : Spec (CommRingCat.of R) ⟶ S), IsOpenImmersion f →
    PreservesFilteredColimitsOfSize.{u, u} (algebraFunctor f ⋙ F)

/-- Condition (F3): for a complete local noetherian ring `A` over `S` with maximal ideal `m`,
the map `F(Spec A) → lim_n F(Spec A/mⁿ)` is bijective. It is stated as injectivity
together with surjectivity onto compatible families. -/
def AdicLimits : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (f : Spec (CommRingCat.of A) ⟶ S),
    (∀ x y : F.obj (op (Over.mk f)),
      (∀ n : ℕ, F.map (algebraOverBase f (A ⧸ IsLocalRing.maximalIdeal A ^ n)).op x =
        F.map (algebraOverBase f (A ⧸ IsLocalRing.maximalIdeal A ^ n)).op y) → x = y) ∧
    ∀ s : ∀ n : ℕ, F.obj (op (algebraOver f (A ⧸ IsLocalRing.maximalIdeal A ^ n))),
      (∀ n : ℕ, F.map (algHomOver f (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal A) n.le_succ))).op (s (n + 1)) =
        s n) →
      ∃ x : F.obj (op (Over.mk f)), ∀ n : ℕ,
        F.map (algebraOverBase f (A ⧸ IsLocalRing.maximalIdeal A ^ n)).op x = s n

/-- Condition (F4′) of Murre's Corollary 1: let `A` be a local artinian ring with residue
field `k`, `ξ₀ ∈ F(Spec k)`, and `A → A'` injective with `length_A (A'/A) = 1`. If the
image of `ξ₀` in `F(Spec (A' ⊗_A k))` lifts to some `ξ' ∈ F(Spec A')`, then `ξ₀` lifts to
some `ξ ∈ F(Spec A)`. -/
def ArtinianLifting : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (f : Spec (CommRingCat.of A) ⟶ S) (A' : Type u) [CommRing A'] [Algebra A A'],
    Function.Injective (algebraMap A A') →
    Module.length A (A' ⧸ LinearMap.range (Algebra.linearMap A A')) = 1 →
    ∀ (ξ₀ : F.obj (op (algebraOver f (IsLocalRing.ResidueField A))))
      (ξ' : F.obj (op (algebraOver f A'))),
      F.map (algHomOver f (Algebra.TensorProduct.includeLeft :
          A' →ₐ[A] A' ⊗[A] IsLocalRing.ResidueField A)).op ξ' =
        F.map (algHomOver f (Algebra.TensorProduct.includeRight :
          IsLocalRing.ResidueField A →ₐ[A] A' ⊗[A] IsLocalRing.ResidueField A)).op ξ₀ →
      ∃ ξ : F.obj (op (Over.mk f)),
        F.map (algebraOverBase f (IsLocalRing.ResidueField A)).op ξ = ξ₀

/-- Condition (F5) in the strong form of Murre's Corollary 1, for local artinian rings: for a
local artinian ring `A` over `S` and a nilpotent ideal `I`, `F(Spec A) → F(Spec A/I)` is
injective. -/
def NilpotentInjective : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] (I : Ideal A), IsNilpotent I →
    ∀ f : Spec (CommRingCat.of A) ⟶ S,
      Function.Injective (F.map (algebraOverBase f (A ⧸ I)).op)

/-- Condition (F6): for a discrete valuation ring `V` over `S` with fraction field `K`, two
elements of `F(Spec V)` with the same image in `F(Spec K)` are equal. -/
def ValuativeSeparation : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (f : Spec (CommRingCat.of V) ⟶ S),
    Function.Injective (F.map (algebraOverBase f (FractionRing V)).op)

section Lifting

variable {F}
variable {A : Type u} [CommRing A] {f : Spec (CommRingCat.of A) ⟶ S} {I : Ideal A}

/-- The restriction of `ξ' ∈ F(Spec (A/I))` to `Spec (B/IB)`, for an `A`-algebra `B`. -/
def restrictQuotient (B : Type u) [CommRing B] [Algebra A B]
    (ξ' : F.obj (op (algebraOver f (A ⧸ I)))) :
    F.obj (op (algebraOver f (B ⧸ I.map (algebraMap A B)))) :=
  F.map (algHomOver f (Ideal.quotientMapₐ (I.map (algebraMap A B)) (Algebra.ofId A B)
    (fun _ hx ↦ Ideal.mem_map_of_mem _ hx))).op ξ'

/-- The restriction of `ξ'` to `Spec (B/IB)` lifts to `Spec B`. -/
def LiftsTo (B : Type u) [CommRing B] [Algebra A B]
    (ξ' : F.obj (op (algebraOver f (A ⧸ I)))) : Prop :=
  ∃ η : F.obj (op (algebraOver f B)),
    F.map (algHomOver f (Ideal.Quotient.mkₐ A (I.map (algebraMap A B)))).op η =
      restrictQuotient B ξ'

/-- The restriction of `ξ'` to `Spec (B/IB)` lifts to no closed subscheme `Spec (B/J)` of
`Spec B` strictly larger than `Spec (B/IB)`, that is, to none with `J < IB`. -/
def NoLargerLift (B : Type u) [CommRing B] [Algebra A B]
    (ξ' : F.obj (op (algebraOver f (A ⧸ I)))) : Prop :=
  ∀ (J : Ideal B) (hJ : J < I.map (algebraMap A B)) (η : F.obj (op (algebraOver f (B ⧸ J)))),
    F.map (algHomOver f (Ideal.Quotient.factorₐ A hJ.le)).op η ≠ restrictQuotient B ξ'

end Lifting

/-- Condition (F7): let `A` be a complete local noetherian ring over `S` of dimension `1` with
only one associated prime, `t` the generic point of `T = Spec A`, `I` a nilpotent ideal with
`N · I = 0` for the nilradical `N`, and `ξ' ∈ F(Spec (A/I))`. If the restriction of `ξ'` to
`Spec (A/I)_t` lifts to `Spec A_t`, then `ξ'` lifts to `Spec A`. -/
def OneDimensionalLifting : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A],
    ringKrullDim A = 1 → (∃ p : Ideal A, associatedPrimes A A = {p}) →
    ∀ t : PrimeSpectrum A, IsGenericPoint t Set.univ →
    ∀ I : Ideal A, IsNilpotent I → nilradical A * I = ⊥ →
    ∀ (f : Spec (CommRingCat.of A) ⟶ S) (ξ' : F.obj (op (algebraOver f (A ⧸ I)))),
      LiftsTo (Localization.AtPrime t.asIdeal) ξ' →
      ∃ ξ : F.obj (op (Over.mk f)), F.map (algebraOverBase f (A ⧸ I)).op ξ = ξ'

/-- Condition (F8): let `A` be a noetherian ring over `S` with `T = Spec A` irreducible of
generic point `t`, `I` a nilpotent ideal with `I · N = 0`, and `ξ' ∈ F(Spec (A/I))`. If the
restriction of `ξ'` to `Spec (A/I)_t` lifts to no subscheme of `Spec A_t` strictly larger
than `Spec (A/I)_t`, then there is a nonempty open `W ⊆ T` such that, for every open
`W₁ ⊆ W`, the restriction of `ξ'` to `W₁ ×_T Spec (A/I)` lifts to no subscheme of `W₁`
strictly larger. The opens are taken basic, `W = D(g₀)` and `W₁ = D(g)`. -/
def GenericNonLifting : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (t : PrimeSpectrum A),
    IsGenericPoint t Set.univ →
    ∀ I : Ideal A, IsNilpotent I → I * nilradical A = ⊥ →
    ∀ (f : Spec (CommRingCat.of A) ⟶ S) (ξ' : F.obj (op (algebraOver f (A ⧸ I)))),
      NoLargerLift (Localization.AtPrime t.asIdeal) ξ' →
      ∃ g₀ : A, (PrimeSpectrum.basicOpen g₀ : Set (PrimeSpectrum A)).Nonempty ∧
        ∀ g : A, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen g₀ →
          NoLargerLift (Localization.Away g) ξ'

/-- Murre's criterion (Bourbaki exp. 294, Theorem 1 in the form of its Corollary 1,
sufficiency direction): over a locally noetherian scheme `S`, a presheaf on `Over S` with
`u`-small values satisfying (F1a), (F1b), (F2), (F3), (F4′), strong (F5), (F6), (F7) and
(F8) is represented by a scheme that is separated, locally of finite type and formally
unramified over `S`. This defines the proposition; it does not prove it. -/
def MurreCriterionStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (F : (Over S)ᵒᵖ ⥤ Type v),
    SmallValues F → ZariskiSheaf F → FaithfullyFlatSheaf F → FilteredColimits F →
    AdicLimits F → ArtinianLifting F → NilpotentInjective F → ValuativeSeparation F →
    OneDimensionalLifting F → GenericNonLifting F →
    ∃ (Y : Scheme.{u}) (q : Y ⟶ S),
      Nonempty (F.RepresentableBy (Over.mk q)) ∧
        IsSeparated q ∧ LocallyOfFiniteType q ∧ FormallyUnramified q

end Langlands.AlgebraicGeometry.UnramifiedFunctor
