/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Topology.Constructible
public import WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Topology.Stratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Constructible sheaves on the small étale site

Let `X` be a scheme and let `F` be a sheaf on the small étale site of `X` (see
`AlgebraicGeometry.Scheme.smallEtaleTopology`) with values in a category `A`. Following
[SGA 4, Exp. IX, §2] we define:

- `F` is *constant* if it is isomorphic to the sheafification of a constant presheaf;
  this is mathlib's `CategoryTheory.Sheaf.IsConstant`.
- `F` is *locally constant* (`IsLocallyConstantSheaf`) if there is an étale cover of `X`
  (a jointly surjective family of étale maps `Uᵢ ⟶ X`, a cover in
  `Scheme.etalePrecoverage`) such that the restriction of `F` to each `Uᵢ` is constant;
  the trivializing data is packaged in `LocallyConstantDatum`. A constant sheaf is
  locally constant, trivialized by the identity cover
  (`CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf`).
- `F` is *finite* (`IsFiniteSheaf`) if the stalk of `F` at every geometric point of `X`
  (`Scheme.pointSmallEtale`) is finitely generated
  (`CategoryTheory.ConcreteCategory.IsFinitelyGenerated`): a finitely generated module for
  sheaves of modules, a finite set for sheaves of sets, a finite module over a finite ring.
- `F` is *finite locally constant* (`IsFiniteLocallyConstantSheaf`) if it is locally
  constant and finite.
- `F` is *constructible* (`IsConstructibleSheaf`) if there is a stratification of `X`
  (`Scheme.Stratification`: a stratification of the underlying topological space of `X` —
  a finite partition into locally closed subsets, `Topology.Stratification`, following
  [Stacks 09XZ], whose strata are constructible subsets — together with schemes immersed in
  `X` realizing the strata) such that
  the pullback of `F` to each stratum is finite locally constant.

All four predicates are `Prop`-valued classes.

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
Grothendieck abelian category with small-site sheafification
(`CategoryTheory.HasSmallSiteSheafify`) and `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes; the class is what supplies the sheafification used
to restrict a sheaf to a member of an étale cover, see the implementation notes. The notions
involving finiteness require `A` to be moreover concrete, finite generation referring to the
elements of the underlying type `CategoryTheory.ToType`. This covers sheaves of abelian groups
(`A = Ab.{u + 1}`) and of `Λ`-modules (`A = ModuleCat.{u + 1} Λ`), for all the coefficient
stages of the `ℓ`-adic formalism: the finite rings `Λₙ = 𝒪_E/ϖⁿ`, the valuation rings `𝒪_E` and
the fields `E` and `ℚ̄_ℓ`. Over a finite ring a finitely
generated module is finite; over a field it is finite-dimensional, so constructible sheaves over a
field are not forced to vanish.

To restrict `F` to an étale `U ⟶ X` we use the localized site: `F.over U` is the sheaf
induced by `F` on the localization of the small étale site at `U`, which is equivalent to
the small étale site of `U`. To restrict `F` to a stratum we use the pullback
`AlgebraicGeometry.Etale.upperStar` of `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
along an immersion, the left adjoint of the pushforward `AlgebraicGeometry.Etale.lowerStar`.

## Implementation notes

- The pullback `Etale.upperStar` is defined by left Kan extension along base change
  followed by sheafification. The Kan extensions in question exist for an arbitrary `f`
  without any smallness of the full small étale site, by the instance
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
  `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`: the indexing comma
  categories have objects in `Type (u + 1)` and `Hom`-types in `Type u`, and `A` has all
  colimits of size `u + 1`.
- Sheafification is likewise not assumed here. Restricting a sheaf to a member of an étale
  cover needs it for the *localizations* of the small étale sites, and for a Grothendieck
  abelian `A` it is supplied by the instance
  `CategoryTheory.GrothendieckTopology.hasSheafify_over_smallEtaleTopology` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, a slice of an
  essentially small site being again essentially small; it is a case of
  `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` there. This replaces
  what used to be a `HasWeakSheafify` hypothesis quantified over all schemes and all étale `U`, the
  quantification being forced by the existential quantifier over stratifications.
- Similarly, `CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf` assumes the
  existence of the right Kan extensions along `(Over.forget U).op` needed to compare
  sheafification on the small étale site with sheafification on its localizations.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

section PullbackFunctor

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The pullback of étale sheaves along `f : X ⟶ Y` sends constant sheaves to constant
sheaves: `constantSheaf ⋙ f^*` and `constantSheaf` are both left adjoint to global
sections of the pushforward, since base change preserves the terminal object of the
small étale site (`X ×_Y Y ≅ X`). -/
def upperStarConstantSheafIso (f : X ⟶ Y) :
    constantSheaf Y.smallEtaleTopology A ⋙ Etale.upperStar A f ≅
      constantSheaf X.smallEtaleTopology A :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).comp
        (Etale.upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (Etale.lowerStarCompSheafSectionsTerminalIso A f))
    (constantSheafAdj X.smallEtaleTopology A terminalIsTerminal)

end PullbackFunctor

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The object of the small étale site of `X` given by a member of an étale cover
of `X`. -/
abbrev Cover.etalePrecoverageToEtale (𝒰 : Cover.{u} etalePrecoverage X) (i : 𝒰.I₀) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (𝒰.f i) (𝒰.map_prop i)

/-- The datum of a trivialization of a sheaf `F` on the small étale site of `X`: an étale
cover of `X` — a jointly surjective family of étale maps, a cover in
`Scheme.etalePrecoverage` — such that the restriction of `F` to the site localized at
each member of the cover is constant in the sense of `CategoryTheory.Sheaf.IsConstant`.
`F` is locally constant if such a datum exists, see `IsLocallyConstantSheaf`. -/
structure LocallyConstantDatum (F : Sheaf X.smallEtaleTopology A) where
  /-- The trivializing étale cover. -/
  cover : Cover.{u} etalePrecoverage X
  /-- The restriction of `F` to the site localized at each member of the cover is
  constant. -/
  isConstant (i : cover.I₀) : (F.over (cover.etalePrecoverageToEtale i)).IsConstant
    (X.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))

/-- A sheaf `F` on the small étale site of `X` is *locally constant* if there is an étale
cover of `X` trivializing `F`, i.e. a `LocallyConstantDatum`. Applies to sheaves of
abelian groups (`A = Ab.{u + 1}`), of `Λ`-modules (`A = ModuleCat.{u + 1} Λ`), etc. -/
class IsLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop where
  nonempty_locallyConstantDatum : Nonempty (LocallyConstantDatum F)

omit [HasSmallSiteSheafify A] in
/-- A constant sheaf on the small étale site is locally constant, trivialized by the
identity cover. The right Kan extension hypothesis compares sheafification on the small
étale site with sheafification on its localizations; it always holds mathematically, see
the module implementation notes. -/
lemma _root_.CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf
    [∀ (U : X.Etale) (P : (Over U)ᵒᵖ ⥤ A), (Over.forget U).op.HasPointwiseRightKanExtension P]
    {F : Sheaf X.smallEtaleTopology A} (h : F.IsConstant X.smallEtaleTopology) :
    IsLocallyConstantSheaf F :=
  have := h
  have : etalePrecoverage.{u}.HasIsos := inferInstanceAs (precoverage @Etale).HasIsos
  ⟨⟨⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ F.isConstant_over _⟩⟩⟩

/-- A sheaf `F` on the small étale site of `X` is an *irreducible local system* if it is locally
constant and nonzero, and every locally constant subsheaf of `F` is zero or all of `F`. For a
lisse sheaf on a connected scheme this says that the corresponding representation of the étale
fundamental group is irreducible. -/
def IsIrreducibleLocalSystem (F : Sheaf X.smallEtaleTopology A) : Prop :=
  IsLocallyConstantSheaf F ∧ ¬ IsZero F ∧
    ∀ (G : Sheaf X.smallEtaleTopology A) (ι : G ⟶ F), Mono ι → IsLocallyConstantSheaf G →
      IsZero G ∨ IsIso ι

end LocallyConstant

section FiniteSheaf

variable {A : Type u'} [Category.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasColimitsOfSize.{u, u} A]

/-- A sheaf `F` on the small étale site of `X` with values in a concrete category is
*finite* if the stalk of `F` at every geometric point of `X` is finitely generated
(`CategoryTheory.ConcreteCategory.IsFinitelyGenerated`): for sheaves of `Λ`-modules the stalks
are finitely generated `Λ`-modules (`ModuleCat.isFinitelyGenerated_iff`), for sheaves of sets
they are finite sets (`CategoryTheory.ConcreteCategory.isFinitelyGenerated_iff_finite`). Over a
finite ring `Λ` this says that the stalks are finite. For sheaves of `Λ`-modules it is
equivalent to every stalk receiving an epimorphism `Λ^n ⟶ F_s̄` from a finite free module
(`AlgebraicGeometry.Scheme.isFiniteSheaf_iff_exists_epi`), the element-free form to which this
definition can be switched. A geometric point `Spec Ω ⟶ X`, with `Ω` a
separably closed field, induces a point of the small étale site (`Scheme.pointSmallEtale`), and
the stalk of `F` is its fiber `CategoryTheory.GrothendieckTopology.Point.sheafFiber` at this
point. -/
class IsFiniteSheaf (F : Sheaf X.smallEtaleTopology A) : Prop where
  isFinitelyGenerated_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    ConcreteCategory.IsFinitelyGenerated ((pointSmallEtale s).sheafFiber.obj F)

/-- **Finite sheaves of modules via epimorphisms from finite free modules.** A sheaf of
`Λ`-modules on the small étale site of `X` is finite if and only if each of its stalks at a
geometric point receives an epimorphism `Λ^n ⟶ F_s̄` from a finite free `Λ`-module
(`ModuleCat.isFinitelyGenerated_iff_exists_epi`). The right-hand side is a definition of
finiteness that does not refer to elements of the stalks, to which `IsFiniteSheaf` can be
switched. -/
lemma isFiniteSheaf_iff_exists_epi {Λ : Type (u + 1)} [Ring Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsFiniteSheaf F ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ (n : ℕ) (f : ModuleCat.of Λ (Fin n → Λ) ⟶ (pointSmallEtale s).sheafFiber.obj F),
        Epi f :=
  ⟨fun h Ω _ _ s ↦ (ModuleCat.isFinitelyGenerated_iff_exists_epi _).1
      (h.isFinitelyGenerated_sheafFiber Ω s),
    fun h ↦ ⟨fun Ω _ _ s ↦ (ModuleCat.isFinitelyGenerated_iff_exists_epi _).2 (h Ω s)⟩⟩

end FiniteSheaf

section FiniteLocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Blueprint `definition-lisse-sheaves--1`: Finite locally constant sheaves.

A sheaf `F` on the small étale site of `X` with values in a concrete category is
*finite locally constant* if it is locally constant and finite, that is, with finitely
generated stalks (`IsFiniteSheaf`). For sheaves of sets,
equivalently (not proved here), `F` is representable by a scheme finite étale over
`X`. For sheaves of `Λ`-modules, the blueprint's rank one condition (the local constant values
can be chosen free of rank one) is, for a locally constant sheaf, the condition that every
geometric stalk is isomorphic to `Λ` (`AlgebraicGeometry.Scheme.HasRankOneStalks`). -/
class IsFiniteLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop
    extends IsLocallyConstantSheaf F, IsFiniteSheaf F

end FiniteLocallyConstant

section Stratification

/-- A *stratification* of a scheme `X`: a stratification of the underlying topological
space of `X` (`Topology.Stratification`: a finite partition into *constructible* locally closed
subsets — `Topology.IsConstructible`, in the Boolean algebra generated by the retrocompact open
subsets — following [Stacks 09XZ] and [Stacks 03RW]), together with, for each stratum, a
scheme immersed in `X` with set-theoretic image the stratum. A sheaf on the small étale site
of `X` is constructible if its pullbacks to the strata of some stratification are finite
locally constant, see `IsConstructibleSheaf`.

Constructibility of the strata (`Topology.Stratification.isConstructible_stratum`) is part of
the definition of a constructible sheaf [Stacks 03RW, 095E]: without it, on a non-noetherian
quasi-compact `X` with a non-quasi-compact open `U`, the extension by zero of the constant sheaf
on `U` would be constructible, and on `X = Spec ∏ 𝔽₂` the skyscraper sheaf at a closed non-open
point would be. On a noetherian scheme every locally closed subset is constructible, and
`Stratification.ofNoetherianSpace` builds a stratification from locally closed strata alone. -/
structure Stratification (X : Scheme.{u}) extends Topology.Stratification X where
  /-- The schemes underlying the strata. -/
  domain : Fin n → Scheme.{u}
  /-- The immersions of the strata into `X`. -/
  immersion : ∀ i, domain i ⟶ X
  isImmersion : ∀ i, IsImmersion (immersion i) := by infer_instance
  range_immersion : ∀ i, Set.range (immersion i) = stratum i

attribute [instance] Stratification.isImmersion

/-- **Stratifications of a Noetherian scheme from locally closed strata.** On a Noetherian
space every locally closed subset is constructible
(`IsLocallyClosed.isConstructible_of_noetherianSpace`), so a stratification of a scheme `X`
with Noetherian underlying space — for instance a Noetherian scheme, `IsNoetherian X` — is
determined by finitely many locally closed strata and the schemes immersed in `X` realizing
them. -/
@[simps n stratum domain immersion]
def Stratification.ofNoetherianSpace [TopologicalSpace.NoetherianSpace X] (n : ℕ)
    (stratum : Fin n → Set X) (isLocallyClosed_stratum : ∀ i, IsLocallyClosed (stratum i))
    (iUnion_stratum_eq_univ : ⋃ i, stratum i = Set.univ)
    (pairwise_disjoint_stratum : Pairwise (Function.onFun Disjoint stratum))
    (domain : Fin n → Scheme.{u}) (immersion : ∀ i, domain i ⟶ X)
    (isImmersion : ∀ i, IsImmersion (immersion i) := by infer_instance)
    (range_immersion : ∀ i, Set.range (immersion i) = stratum i) : Stratification X where
  n := n
  stratum := stratum
  isLocallyClosed_stratum := isLocallyClosed_stratum
  isConstructible_stratum i := (isLocallyClosed_stratum i).isConstructible_of_noetherianSpace
  iUnion_stratum_eq_univ := iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := pairwise_disjoint_stratum
  domain := domain
  immersion := immersion
  isImmersion := isImmersion
  range_immersion := range_immersion

end Stratification

section Constructible

variable {A : Type u'} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

/-- A sheaf `F` on the small étale site of `X` with values in a concrete category is
*constructible* if there is a stratification of `X` such that the pullback of `F` to each
stratum is finite locally constant.

The stratification records a choice of scheme structure on each stratum via the immersion
`S.immersion i : S.domain i ⟶ X`; by topological invariance of the small étale site the
condition does not depend on this choice.

The left Kan extensions along base change needed by the pullback `Etale.upperStar` are
provided by the instance
`CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
`WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`. Stating
`IsFiniteLocallyConstantSheaf` needs sheafification for the localizations of the small
étale sites of the strata; since the stratification is existentially quantified, this has
to be available for all schemes, which is what the hypothesis
`CategoryTheory.HasSmallSiteSheafify A` provides (see the module implementation notes).

The strata are constructible subsets (`Topology.Stratification.isConstructible_stratum`), as
in [Stacks 03RW]. Every sheaf constructible in the present sense is constructible in the
affine-local sense of loc. cit.: the traces of the strata on an affine open `U` form a
stratification of `U` (preimages of constructible subsets along morphisms of schemes are
constructible, `AlgebraicGeometry.Scheme.Hom.isConstructible_preimage`). For `X`
quasi-compact and quasi-separated the converse holds, so this global definition agrees with
[Stacks 03RW] and with [Stacks 095E]: the decompositions of the members of a finite affine open
cover, whose members are retrocompact, have a common refinement by constructible locally closed
subsets of `X`. For a general `X` the present definition is stronger: it asks for a single
finite stratification of all of `X`, whereas loc. cit. lets the decomposition depend on the
affine open. For instance let `Λ` be a nonzero coefficient ring, let `X` be the disjoint union
over `n` of the affine spaces `𝔸ⁿ` over a field, each with a flag `𝔸ⁿ = Z₀ ⊃ Z₁ ⊃ ⋯ ⊃ Zₙ` of
irreducible closed subsets, and let `F` be on `𝔸ⁿ` the direct sum of the pushforwards of the
constant sheaf `Λ` from the `Zᵢ`, so that the stalk of `F` at the generic point of `Zᵢ` is
free of rank `i + 1` over `Λ`. A subset of `X` on
which `F` is locally constant cannot contain the generic points of two members of a flag (the
later one is a specialization of the earlier one, so every neighbourhood of it in the subset
contains the earlier one, where the rank differs), so a stratification trivializing `F` has at
least `n + 1` strata meeting `𝔸ⁿ` for every `n`, and there is no finite one; whereas every
affine open of `X` meets finitely many `𝔸ⁿ` and `F` is constructible on it in the sense of
loc. cit. For sheaves of modules over a noetherian ring, the pullbacks to the strata being
locally constant of finite type, it is the constructibility of sheaves of modules of the Stacks
project. In the `ℓ`-adic formalism it is applied with `A = ModuleCat Λ` for the coefficient
stages `Λ` of `definition-constructible-sheaves--6`.

Over a scheme with Noetherian underlying space the constructibility of the strata is automatic,
see `IsConstructibleSheaf.of_noetherianSpace`. -/
class IsConstructibleSheaf (F : Sheaf X.smallEtaleTopology A) : Prop where
  exists_stratification : ∃ S : Stratification X, ∀ i : Fin S.n,
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion i)).obj F)

omit [HasSmallSiteSheafify A] in
/-- **Constructibility over a Noetherian scheme from locally closed strata.** A sheaf `F` on a
scheme `X` with Noetherian underlying space — for instance a Noetherian scheme,
`IsNoetherian X` — is constructible as soon as, for some finite partition of `X` into locally
closed subsets realized by schemes `domain i` immersed in `X`, the pullbacks of `F` to the
`domain i` are finite locally constant: on a Noetherian space every locally closed subset is
constructible, so no constructibility of the strata has to be checked. -/
theorem IsConstructibleSheaf.of_noetherianSpace [TopologicalSpace.NoetherianSpace X]
    (F : Sheaf X.smallEtaleTopology A) {n : ℕ} (stratum : Fin n → Set X)
    (isLocallyClosed_stratum : ∀ i, IsLocallyClosed (stratum i))
    (iUnion_stratum_eq_univ : ⋃ i, stratum i = Set.univ)
    (pairwise_disjoint_stratum : Pairwise (Function.onFun Disjoint stratum))
    {domain : Fin n → Scheme.{u}} (immersion : ∀ i, domain i ⟶ X)
    [∀ i, IsImmersion (immersion i)] (range_immersion : ∀ i, Set.range (immersion i) = stratum i)
    (hF : ∀ i, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (immersion i)).obj F)) :
    IsConstructibleSheaf F :=
  ⟨Stratification.ofNoetherianSpace n stratum isLocallyClosed_stratum iUnion_stratum_eq_univ
    pairwise_disjoint_stratum domain immersion inferInstance range_immersion, hF⟩

end Constructible

end Scheme

end AlgebraicGeometry
