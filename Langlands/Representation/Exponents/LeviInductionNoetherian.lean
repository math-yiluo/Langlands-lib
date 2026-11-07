import Langlands.Representation.Exponents.LeviInductionEmbeddings
import Langlands.Representation.Category.SmoothCoproducts
import Mathlib.RingTheory.Noetherian.Basic

/-! # Noetherianity of inductions from an actual represented Levi along embeddings

Let `ρ` be a smooth representation of `M(F)` that embeds into a finite direct sum of
smooth representations `B j`, or more generally admits a finite jointly injective family of
intertwiners `ρ → B j`. If every normalized induction `i_P^G(B j)` has a Noetherian
group-algebra module, then so does `i_P^G(ρ)`, and in particular `i_P^G(ρ)` is finitely
generated over `ℂ[G(F)]`. This is the descent part of the general step in the proof of
Renard VI.7.5, Theorem: Noetherianity passes from the inductions of the summands to the
induction of `ρ`.
-/

noncomputable section

universe u v w uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidAlgebra

namespace Langlands.NoetherianRepresentation

universe uR uG uV uW

variable {k : Type uR} [CommRing k] {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module k V]

/-- A family of intertwiners `f i : ρ → σ i`, assembled into one `k[G]`-linear map from the
group-algebra module of `ρ` into the product of the group-algebra modules of the `σ i`. -/
def piMap {J : Type uI} {W : J → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    {ρ : Representation k G V} {σ : ∀ i, Representation k G (W i)}
    (f : ∀ i, ρ.IntertwiningMap (σ i)) : ρ.asModule →ₗ[k[G]] ∀ i, (σ i).asModule :=
  LinearMap.pi fun i => Representation.IntertwiningMap.equivLinearMapAsModule ρ (σ i) (f i)

/-- The `i`th component of `piMap f v` is `f i v`. -/
@[simp]
theorem piMap_apply {J : Type uI} {W : J → Type uW} [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] {ρ : Representation k G V} {σ : ∀ i, Representation k G (W i)}
    (f : ∀ i, ρ.IntertwiningMap (σ i)) (v : V) (i : J) : piMap f v i = f i v :=
  rfl

/-- The assembled map is injective exactly when the family is jointly injective. -/
theorem piMap_injective_iff {J : Type uI} {W : J → Type uW} [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] {ρ : Representation k G V} {σ : ∀ i, Representation k G (W i)}
    (f : ∀ i, ρ.IntertwiningMap (σ i)) :
    Function.Injective (piMap f) ↔ ∀ x y, (∀ i, f i x = f i y) → x = y :=
  ⟨fun h _ _ hxy => h (funext hxy), fun h x y hxy => h x y fun i => congrFun hxy i⟩

/-- A representation with a finite jointly injective family of intertwiners into
Noetherian representations is Noetherian. -/
theorem of_jointlyInjective {J : Type uI} [Finite J] {W : J → Type uW}
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] {ρ : Representation k G V}
    {σ : ∀ i, Representation k G (W i)} (f : ∀ i, ρ.IntertwiningMap (σ i))
    (hf : ∀ x y, (∀ i, f i x = f i y) → x = y)
    [∀ i, IsNoetherian k[G] (σ i).asModule] : IsNoetherian k[G] ρ.asModule :=
  isNoetherian_of_injective (piMap f) ((piMap_injective_iff f).mpr hf)

end Langlands.NoetherianRepresentation

namespace Langlands.SmoothRep

universe uG uV uW

/-- The components of an injective intertwiner into an actual direct sum of smooth
representations are jointly injective. -/
theorem directSum_components_jointlyInjective {H : Type uG} [Group H] [TopologicalSpace H]
    {J : Type uI} [DecidableEq J] {A : SmoothRep.{0, uG, uV} ℂ H}
    (B : J → SmoothRep.{0, uG, max uI uW} ℂ H)
    (f : A.representation.IntertwiningMap (directSum B).representation)
    (hf : Function.Injective f) :
    ∀ x y, (∀ i, (hom (directSumπ B i)).comp f x = (hom (directSumπ B i)).comp f y) →
      x = y :=
  fun _ _ h => hf (DirectSum.ext_component ℂ fun i => h i)

end Langlands.SmoothRep

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]

local instance leviInductionNoetherianAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

local instance leviInductionNoetherianSourceTopology :
    TopologicalSpace (rationalPoints M) := RationalPointFamily.pointTopology

/-- Induction from the actual Levi points preserves joint injectivity of a family of
coefficient intertwiners: induced functions are compared pointwise. -/
theorem leviInductionMap_jointlyInjective {J : Type uI}
    {A : SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    {B : J → SmoothRep.{0, u, w} ℂ (rationalPoints M)}
    (f : ∀ i, A.representation.IntertwiningMap (B i).representation)
    (hf : ∀ x y, (∀ i, f i x = f i y) → x = y) :
    ∀ x y, (∀ i, leviInductionMap p l r hp hl hr hmul (f i) x =
      leviInductionMap p l r hp hl hr hmul (f i) y) → x = y := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact hf _ _ fun i => congrArg (fun z => z.1.1 g) (h i)

/-- Descent in the general step of Renard VI.7.5, Theorem: if a smooth representation `A`
of `M(F)` has a finite jointly injective family of intertwiners `f i : A → B i` and every
induction `i_P^G(B i)` is Noetherian over `ℂ[G(F)]`, then `i_P^G(A)` is Noetherian. -/
theorem leviInduction_isNoetherian_of_jointlyInjective {J : Type uI} [Finite J]
    {A : SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    {B : J → SmoothRep.{0, u, w} ℂ (rationalPoints M)}
    (f : ∀ i, A.representation.IntertwiningMap (B i).representation)
    (hf : ∀ x y, (∀ i, f i x = f i y) → x = y)
    (hB : ∀ i, IsNoetherian ℂ[rationalPoints G]
      ((leviInductionFunctor.{u, w} p l r hp hr hl hmul).obj (B i)).representation.asModule) :
    IsNoetherian ℂ[rationalPoints G]
      ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj A).representation.asModule :=
  NoetherianRepresentation.of_jointlyInjective
    (fun i => leviInductionMap p l r hp hl hr hmul (f i))
    (leviInductionMap_jointlyInjective p l r hp hl hr hmul f hf)

/-- Descent in the general step of Renard VI.7.5, Theorem, for an embedding into an actual
finite direct sum: if `A ↪ ⊕ B i` with `J` finite and every `i_P^G(B i)` is Noetherian,
then `i_P^G(A)` is Noetherian. -/
theorem leviInduction_isNoetherian_of_injective_directSum {J : Type uI} [DecidableEq J]
    [Finite J] {A : SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (B : J → SmoothRep.{0, u, max uI w} ℂ (rationalPoints M))
    (f : A.representation.IntertwiningMap (SmoothRep.directSum B).representation)
    (hf : Function.Injective f)
    (hB : ∀ i, IsNoetherian ℂ[rationalPoints G]
      ((leviInductionFunctor.{u, max uI w} p l r hp hr hl hmul).obj
        (B i)).representation.asModule) :
    IsNoetherian ℂ[rationalPoints G]
      ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj A).representation.asModule :=
  leviInduction_isNoetherian_of_jointlyInjective p l r hp hl hr hmul
    (fun i => (SmoothRep.hom (SmoothRep.directSumπ B i)).comp f)
    (SmoothRep.directSum_components_jointlyInjective B f hf) hB

/-- Finite generation form of the general step: under the hypotheses of
`leviInduction_isNoetherian_of_injective_directSum`, the induction `i_P^G(A)` is finitely
generated over `ℂ[G(F)]`. -/
theorem leviInduction_finite_of_injective_directSum {J : Type uI} [DecidableEq J]
    [Finite J] {A : SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (B : J → SmoothRep.{0, u, max uI w} ℂ (rationalPoints M))
    (f : A.representation.IntertwiningMap (SmoothRep.directSum B).representation)
    (hf : Function.Injective f)
    (hB : ∀ i, IsNoetherian ℂ[rationalPoints G]
      ((leviInductionFunctor.{u, max uI w} p l r hp hr hl hmul).obj
        (B i)).representation.asModule) :
    Module.Finite ℂ[rationalPoints G]
      ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj A).representation.asModule :=
  have := leviInduction_isNoetherian_of_injective_directSum p l r hp hl hr hmul B f hf hB
  inferInstance

end Langlands.Aubert.General.RepresentedParabolic
