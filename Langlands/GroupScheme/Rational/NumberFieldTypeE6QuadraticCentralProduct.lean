import Langlands.Algebra.NumberFieldReducedNormLocalityProof
import Langlands.GroupScheme.Rational.NumberFieldTypeE6QuadraticLeviReduction
import Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction
import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction
import Langlands.GroupScheme.Rational.CentralCubeKernelQuadraticLift
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAbsolute
import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesInjectivity
import Langlands.FieldTheory.RealAlgebraicClosure
import Langlands.Global.Arithmetic.ArchimedeanAlgebraicClosure

/-! # The type `E_6` Levi Hasse statement from a central product of type `A₂` groups

Platonov–Rapinchuk, §6.8 (printed pp. 383–385), Lemma 6.33 and the construction preceding it.
For a simply connected group `G` of type `E_6` over a number field `F`, the source takes the
Levi subgroup `C₁` of a parabolic subgroup of type `Π ∖ {α₂, α₄}` and constructs
`D = H · B ⊇ C₁`, where `H = [C₁, C₁]` is simply connected of type `A₂ × A₂`. The source
writes `B = Z_G(H)` on printed p. 384. The simply connected type `A₂` factor in the
construction is the identity component `B = Z_G(H)°`. The full centralizer meets `H` in
`Z(H)`, of order `9` over an algebraic closure. For the product map `H × B → D` with
connected `B`, the proof of Lemma 6.33 uses that the kernel `H ∩ B` has order dividing `3`.

The hypotheses here are those of `NumberFieldTypeE6QuadraticLeviHasseStatement`: the vertices
`α₂` and `α₄` are distinguished over a quadratic Galois extension `E/F`, and `C ⟶ G` is the
Levi subgroup `C_E = P ∩ σ(P)` of a minimal parabolic subgroup `P` of `G_E`. Under them, `C`
lies in such a Levi subgroup `C₁` defined over `F` (every automorphism of the `E_6` diagram
fixes `α₂` and `α₄`), and a computation of cocharacter lattices shows that the kernel `H ∩ B`
for `B = Z_G(H)°` has order exactly `3`. The Markdown of the module
`Langlands.GroupScheme.Rational.NumberFieldTypeE6QuadraticLeviReduction` gives this derivation.

This module records the resulting data as the structure `TypeA2CentralIsogenyFactorization`
(a factorization of `C ⟶ G` through the target of a central isogeny from a finite product of
Weil restrictions of simply connected absolutely almost-simple groups of type `A₂`, whose
kernel points over fields have cube one), states its existence as
`NumberFieldTypeE6QuadraticLeviCentralProductStatement`, and proves
`numberFieldTypeE6QuadraticLeviHasse_of_centralProduct`: this statement and
`NumberFieldOuterTypeAHasseStatement` give `NumberFieldTypeE6QuadraticLeviHasseStatement`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- The Hasse principle for simply connected absolutely almost-simple groups of type `A_n`
over a number field, inner or outer: inner forms by the locality of reduced norms, outer forms
by `NumberFieldOuterTypeAHasseStatement`. -/
theorem Cocycle.isTrivial_of_locallyTrivial_typeA
    (houter : NumberFieldOuterTypeAHasseStatement.{u})
    {F : Type u} [Field F] [NumberField F]
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] (hsc : IsSimplyConnected H)
    (habs : IsAbsolutelyAlmostSimple H) (d : TitsIndexData H) {n : ℕ} (hn : 0 < n)
    (e : d.Vertex ≃ Fin n) (hCartan : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle H (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  by_cases hstar : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex),
      d.star σ a = a
  · exact numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality
      Langlands.CentralSimple.numberFieldReducedNormLocality F H d n hsc habs
      ⟨hn, ⟨e, hCartan⟩, hstar⟩ L ξ hξ
  · push Not at hstar
    exact houter F H d n e hsc habs hCartan hstar L ξ hξ

/-- A decomposition of `X` as a finite product of Weil restrictions `R_{Bᵢ/F}(Hᵢ)` of simply
connected absolutely almost-simple groups `Hᵢ` of type `A₂` over finite extensions `Bᵢ/F`. -/
structure TypeA2WeilProduct {F : Type u} [Field F]
    (X : GroupScheme (Spec (CommRingCat.of F))) where
  /-- The index set of the factors. -/
  Index : Type u
  [finite : Finite Index]
  /-- The field `Bᵢ` of definition of the `i`-th factor. -/
  field : Index → Type u
  [isField : ∀ i, Field (field i)]
  [algebra : ∀ i, Algebra F (field i)]
  [finiteDimensional : ∀ i, FiniteDimensional F (field i)]
  /-- The group `Hᵢ` over `Bᵢ`. -/
  factor : ∀ i, GroupScheme (Spec (CommRingCat.of (field i)))
  [isAffineHom : ∀ i, IsAffineHom (factor i).X.hom]
  [isAffine : ∀ i, IsAffine (factor i).X.left]
  [locallyFiniteType : ∀ i, LocallyOfFiniteType (factor i).X.hom]
  simplyConnected : ∀ i, IsSimplyConnected (factor i)
  absolutelyAlmostSimple : ∀ i, IsAbsolutelyAlmostSimple (factor i)
  /-- Tits index data of `Hᵢ`. -/
  index : ∀ i, TitsIndexData (factor i)
  /-- A numbering of the two vertices of the Dynkin diagram of `Hᵢ`. -/
  numbering : ∀ i, (index i).Vertex ≃ Fin 2
  cartan_eq : ∀ i a b, (index i).cartan a b = CartanMatrix.A 2 (numbering i a) (numbering i b)
  /-- The isomorphism of `X` with the product of the Weil restrictions. -/
  iso : X ≅ pi (fun i => AffineWeil.groupScheme F (field i) (factor i))

attribute [instance] TypeA2WeilProduct.finite TypeA2WeilProduct.isField
  TypeA2WeilProduct.algebra TypeA2WeilProduct.finiteDimensional TypeA2WeilProduct.isAffineHom
  TypeA2WeilProduct.isAffine TypeA2WeilProduct.locallyFiniteType

/-- A factorization `C ⟶ D ⟶ G` of `t : C ⟶ G` together with a central isogeny `X ⟶ D` from a
simply connected group `X` that is a finite product of Weil restrictions of absolutely
almost-simple groups of type `A₂`, such that every point of `X` over a field that is killed by
the isogeny has cube one. In Platonov–Rapinchuk, §6.8, `D = H · B` and `X = H × B`. -/
structure TypeA2CentralIsogenyFactorization {F : Type u} [Field F]
    {C G : GroupScheme (Spec (CommRingCat.of F))} (t : C ⟶ G) where
  /-- The intermediate group `D`. -/
  target : GroupScheme (Spec (CommRingCat.of F))
  [isAffineHom : IsAffineHom target.X.hom]
  /-- The homomorphism `D ⟶ G`. -/
  inclusion : target ⟶ G
  /-- The homomorphism `C ⟶ D`. -/
  leviMap : C ⟶ target
  factorization : leviMap ≫ inclusion = t
  /-- The covering group `X`. -/
  source : GroupScheme (Spec (CommRingCat.of F))
  /-- The central isogeny `X ⟶ D`. -/
  isogeny : source ⟶ target
  isCentralIsogeny : IsCentralIsogeny isogeny
  kernel_cube : ∀ (K : Type u) [Field K] [Algebra F K]
    (x : source.affinePoints (CommAlgCat.of F K)),
    source.affinePointsTarget isogeny (CommAlgCat.of F K) x = 1 → x ^ 3 = 1
  simplyConnected : IsSimplyConnected source
  /-- The decomposition of `X` into Weil restrictions of groups of type `A₂`. -/
  product : TypeA2WeilProduct source

attribute [instance] TypeA2CentralIsogenyFactorization.isAffineHom

namespace TypeA2WeilProduct

variable {F : Type u} [Field F] [NumberField F] {X : GroupScheme (Spec (CommRingCat.of F))}

/-- A finite product of Weil restrictions of simply connected absolutely almost-simple groups
of type `A₂` satisfies the Hasse principle on finite Galois covers, given the outer type `A`
Hasse statement. -/
theorem isTrivial_of_locallyTrivial (houter : NumberFieldOuterTypeAHasseStatement.{u})
    (Δ : TypeA2WeilProduct X) {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L]
    [IsGalois F L] (ξ : Cocycle X (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) :
    ξ.IsTrivial := by
  let W := fun i => AffineWeil.groupScheme F (Δ.field i) (Δ.factor i)
  have hprod : (ξ.map Δ.iso.hom).IsTrivial := by
    apply Cocycle.isTrivial_of_pi
    intro i
    let : NumberField (Δ.field i) := NumberField.of_module_finite F (Δ.field i)
    let ζ : Cocycle (W i) (ringTest F L) := (ξ.map Δ.iso.hom).map (Pi.π W i)
    have hζ : ζ.LocallyTrivial := (hξ.map Δ.iso.hom).map (Pi.π W i)
    obtain ⟨E, _, _, _, _, r, hlocal, hreflect⟩ :=
      AffineWeil.exists_finiteGalois_transfer F (Δ.field i) (Δ.factor i) ζ hζ
    exact hreflect (Cocycle.isTrivial_of_locallyTrivial_typeA houter (Δ.simplyConnected i)
      (Δ.absolutelyAlmostSimple i) (Δ.index i) (by norm_num) (Δ.numbering i) (Δ.cartan_eq i)
      ((AffineWeil.transferCocycle F (Δ.field i) (Δ.factor i) ζ).refine r) hlocal)
  obtain ⟨f, hf⟩ := hprod.map Δ.iso.inv
  refine ⟨f, fun a c => ?_⟩
  have hh := hf a c
  change (ξ.toFun a c ≫ Δ.iso.hom.hom.hom) ≫ Δ.iso.inv.hom.hom = _ at hh
  rw [Category.assoc, ← Grp.comp_hom_hom, Δ.iso.hom_inv_id, Grp.id_hom_hom,
    Category.comp_id] at hh
  exact hh

end TypeA2WeilProduct

namespace TypeA2CentralIsogenyFactorization

variable {F : Type u} [Field F] [NumberField F] {C G : GroupScheme (Spec (CommRingCat.of F))}
  {t : C ⟶ G}

/-- A form of Platonov–Rapinchuk, §6.8, Lemma 6.33. Let `t : C ⟶ G` factor through the target
of a central isogeny `X ⟶ D` as in `TypeA2CentralIsogenyFactorization`, and let `E/F` be a
quadratic Galois extension. A cocycle of `C` on the cover `Spec E → Spec F` that is trivial at
every real place has trivial image in `G`, given the outer type `A` Hasse statement.

The proof replaces the source's restriction–corestriction lift and its archimedean vanishing
of `H¹(F_v, H ∩ B)` by cochain computations on the given covers. The image of the cocycle in
`D` is cohomologous to the image of a cocycle `ζ` of `X` on the same quadratic cover; `ζ` is
trivial at the real places since the kernel points are killed by `3` and the local Galois
groups have order `2`, hence trivial at every place because `X` is simply connected, hence
trivial by the Hasse principle for the type `A₂` factors. -/
theorem isTrivial_map (houter : NumberFieldOuterTypeAHasseStatement.{u})
    (P : TypeA2CentralIsogenyFactorization t)
    {E : Type u} [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (hE : Module.finrank F E = 2) (δ : Cocycle C (GaloisCocycle.cover F E))
    (hδ : ∀ w : InfinitePlace F, w.IsReal →
      (δ.baseChangePullback
        (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial) :
    (δ.map t).IsTrivial := by
  have hp := P.isCentralIsogeny
  let : IsAffineHom P.source.X.hom :=
    P.simplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine P.source.X.left := isAffine_of_isAffineHom P.source.X.hom
  let : IsAffine P.target.X.left := isAffine_of_isAffineHom P.target.X.hom
  let ξ := δ.map P.leviMap
  obtain ⟨ζ, hξζ⟩ := hp.exists_cohomologous_map_of_cube_kernel hE P.kernel_cube ξ
  have hreal (w : InfinitePlace F) (hw : w.IsReal) :
      (ζ.baseChangePullback
        (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial := by
    let K := w.Completion
    let M := AlgebraicClosure K
    let : FiniteDimensional K M := Global.finiteArchimedeanAlgebraicClosure F w
    let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
    let : IsGalois K M := isGalois_iff.mpr ⟨inferInstance, ⟨fun _ => IsAlgClosed.splits _⟩⟩
    let j : E →ₐ[F] M := IsAlgClosed.lift
    let : Algebra E M := j.toRingHom.toAlgebra
    let : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    have hM : Module.finrank K M = 2 := Langlands.FieldTheory.finrank_algebraicClosure_of_equiv_real
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
    let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
    have hξw : (ξ.baseChangePullback b).IsTrivial := by
      obtain ⟨f, hf⟩ := (hδ w hw).map ((GroupScheme.baseChange b).map P.leviMap)
      refine ⟨f, fun x y => ?_⟩
      rw [Cocycle.baseChangePullback, Cocycle.baseChange_map_toFun]
      exact hf x y
    have hpw : ((ζ.map P.isogeny).baseChangePullback b).IsTrivial :=
      Cocycle.IsTrivial.of_cohomologous (hξζ.baseChange b _ _) hξw
    exact hp.isTrivial_baseChange_of_cube_kernel (K := K) (M := M) hM (P.kernel_cube M) ζ hpw
  have h1 : (Cocycle.coboundary 1 : Cocycle P.source (GaloisCocycle.cover F E)).IsTrivial :=
    ⟨1, fun _ _ => rfl⟩
  have hcomp := simplyConnectedRealToAllPlacesComparison F P.source P.simplyConnected E
    (Cocycle.coboundary 1) ζ (fun w hw => (h1.baseChange _ _ _).cohomologous (hreal w hw))
  have hloc : ζ.LocallyTrivial := fun v =>
    Cocycle.IsTrivial.of_cohomologous (hcomp v) (h1.baseChange _ _ _)
  have hζ := P.product.isTrivial_of_locallyTrivial houter ζ hloc
  have hξ : ξ.IsTrivial := Cocycle.IsTrivial.of_cohomologous hξζ.symm (hζ.map P.isogeny)
  obtain ⟨f, hf⟩ := hξ.map P.inclusion
  refine ⟨f, fun a c => ?_⟩
  have hh := hf a c
  change (δ.toFun a c ≫ P.leviMap.hom.hom) ≫ P.inclusion.hom.hom = _ at hh
  rw [Category.assoc, ← Grp.comp_hom_hom, P.factorization] at hh
  exact hh

end TypeA2CentralIsogenyFactorization

/-- Under the hypotheses of `NumberFieldTypeE6QuadraticLeviHasseStatement`, the homomorphism
`t : C ⟶ G` from the Levi subgroup of an opposite pair of minimal parabolic subgroups factors
through the target of a central isogeny from a simply connected finite product of Weil
restrictions of absolutely almost-simple groups of type `A₂`, whose kernel points over fields
have cube one.

Derived from the construction preceding Lemma 6.33 in Platonov–Rapinchuk, §6.8: `C` lies in
an `F`-defined Levi subgroup `C₁` of type `Π ∖ {α₂, α₄}` because `α₂` and `α₄` are
distinguished over `E`. For `H = [C₁, C₁]` and `B = Z_G(H)°`, the product `D = H · B`
contains `C₁`, and the map from `X = H × B` to `D` has kernel `H ∩ B` of order `3` by a
computation of cocharacter lattices. -/
def NumberFieldTypeE6QuadraticLeviCentralProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
      (∀ [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
        [LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
        (d' : TitsIndexData ((GroupScheme.baseChange (algebraBaseMap F E)).obj G))
        (e' : d'.Vertex ≃ Fin 6),
        (∀ a b, d'.cartan a b = CartanMatrix.E 6 (e' a) (e' b)) →
        e'.symm 1 ∈ d'.distinguishedVertices ∧ e'.symm 3 ∈ d'.distinguishedVertices) →
      ∀ (C : GroupScheme (Spec (CommRingCat.of F))) (t : C ⟶ G),
        IsQuadraticOppositeMinimalParabolicLevi E t →
        Nonempty (TypeA2CentralIsogenyFactorization t)

/-- The type `E_6` Levi Hasse statement follows from the central product construction and the
outer type `A` Hasse statement. -/
theorem numberFieldTypeE6QuadraticLeviHasse_of_centralProduct
    (hprod : NumberFieldTypeE6QuadraticLeviCentralProductStatement.{u})
    (houter : NumberFieldOuterTypeAHasseStatement.{u}) :
    NumberFieldTypeE6QuadraticLeviHasseStatement.{u} := by
  intro F _ _ G _ _ d e hsc habs hcar E _ _ _ _ hdist C t ht δ hδ
  obtain ⟨P⟩ := hprod F G d e hsc habs hcar E hdist C t ht
  exact P.isTrivial_map houter ht.1 δ hδ

end Langlands.GroupScheme
