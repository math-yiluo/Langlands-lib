/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.FlatBaseDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorFlat

/-! # Stalkwise Tor-independence of base-flat complexes

Source: Stacks Project, perfect.tex, Tag 0A1D, proof checking Tag 0DJ8 (1)
(blueprint: lem-pc-derived-pullback-tor-independent-flat-complex).

The localized comparison of the existing base-derived tensor cohomology model is
used without replacing the canonical map by an arbitrary isomorphism. Its target
is the ordinary tensor stalk complex, canonically the stalk of tensor pullback
by `Scheme.Modules.exists_tensorPullback_stalk_iso`, applied degreewise.
The algebra-map equations specify the actual structure maps of the cartesian square.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Base-flat bounded-above quasi-coherent complexes satisfy the stalkwise condition.

Source: Stacks Project, perfect.tex, Tag 0A1D, proof via Tag 0DJ8 (1)
(blueprint: lem-pc-derived-pullback-tor-independent-flat-complex).

Here x', x, t and f(x) are the points of X_T, X, T and S. The equality f(x) = g(t)
is `pullback.condition` evaluated at x'; the four algebra-map equations fix
R -> A, R -> B and A tensor_R B -> C to the scheme-induced maps. The model M
is arbitrary: its universal counit and comparison equations fix the canonical map
H^i(G_x tensor-derived_R B) tensor_(A tensor_R B) C -> H^i(G_x tensor_A C).
The target is canonically H^i(((g')^*G)_{x'}) by the natural stalk-pullback
isomorphism of lem-weil-pbc-module-stalk-pullback. IsIso is invariant under this
canonical target identification and the tensor symmetry used by extendScalars.
The derived-category instances and cohomology model are presentations, not geometric
assumptions; they exist for all the module categories and complexes in question.

Proof, following the node step by step:
1. Each stalk G_x^n is flat over R by flatness over S and quasi-coherence (01U4).
   The stalk complex is bounded above, so lem-pc-module-bounded-flat-kflat makes it
   K-flat over R.
2. Apply lem-pur-derived-change-of-rings on the one-point site to R -> B.
   The identity K-flat resolution computes the derived tensor by Q tensor_R B.
   The model's counit comparison on cohomology is this canonical identification.
3. The natural stalk-pullback identification gives the target Q tensor_A C,
   compatibly with differentials. The canonical map A tensor_R B -> C is a
   localization by the affine description of fibre products. Localization is exact
   (lem-weil-pbc-localization-module-exact), hence commutes with cohomology.
   Tensor associativity identifies (Q tensor_R B) tensor_(A tensor_R B) C
   with Q tensor_A C. The model's localized_eq pins the comparison to this map,
   which is an isomorphism in every integer degree. -/
theorem derivedPullback_torIndependent_flat_complex
    {S T X : Scheme.{u}} (g : T ⟶ S) (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (G.X i))
    (hqc : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (hflat : ∀ i : ℤ, (G.X i).IsFlatOver f)
    (x' : ↥(pullback f g))
    [Algebra (S.presheaf.stalk (f ((pullback.fst f g) x'))) (X.presheaf.stalk ((pullback.fst f g)
      x'))] [Algebra (S.presheaf.stalk (f ((pullback.fst f g) x'))) (T.presheaf.stalk
      ((pullback.snd f g) x'))] [Algebra ((X.presheaf.stalk ((pullback.fst f g) x'))
      ⊗[(S.presheaf.stalk (f ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g)
      x'))) ((pullback f g).presheaf.stalk x')]
    (hRA : algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x'))) (X.presheaf.stalk
      ((pullback.fst f g) x')) = (f.stalkMap ((pullback.fst f g) x')).hom)
    (hRB : algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x'))) (T.presheaf.stalk
      ((pullback.snd f g) x')) =
      (g.stalkMap ((pullback.snd f g) x')).hom.comp (S.presheaf.stalkCongr (Inseparable.of_eq
        (congrArg (fun φ : pullback f g ⟶ S => φ x') pullback.condition))).hom.hom)
    (hAC : (algebraMap ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f
      ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g) x'))) ((pullback f
      g).presheaf.stalk x')).comp (algebraMap (X.presheaf.stalk ((pullback.fst f g) x'))
      ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f ((pullback.fst f g)
      x')))] (T.presheaf.stalk ((pullback.snd f g) x')))) =
      ((pullback.fst f g).stalkMap x').hom)
    (hBC : (algebraMap ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f
      ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g) x'))) ((pullback f
      g).presheaf.stalk x')).comp
      Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap x').hom)
    [HasDerivedCategory.{w} (ModuleCat.{u} (S.presheaf.stalk (f ((pullback.fst f g) x'))))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (T.presheaf.stalk ((pullback.snd f g) x')))]
    (M : ModuleCat.BaseDerivedTensorCohomologyModel (S.presheaf.stalk (f ((pullback.fst f g) x')))
      (X.presheaf.stalk ((pullback.fst f g) x')) (T.presheaf.stalk ((pullback.snd f g) x'))
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace ((pullback.fst f g)
      x')).mapHomologicalComplex (.up ℤ)).obj G) ((pullback f g).presheaf.stalk x')) :
    ∀ i : ℤ, IsIso (M.localizedComparison i) := by
  have _hqc := hqc
  let Q := ((RingedSpace.moduleStalkFunctor X.toRingedSpace
    ((pullback.fst f g) x')).mapHomologicalComplex (.up ℤ)).obj G
  let P := ((ModuleCat.restrictScalars
    (algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x')))
      (X.presheaf.stalk ((pullback.fst f g) x')))).mapHomologicalComplex (.up ℤ)).obj Q
  have hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i) := by
    obtain ⟨b, hb⟩ := hbounded
    refine ⟨b, fun i hi ↦ ?_⟩
    exact (ModuleCat.restrictScalars _).map_isZero
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace _).map_isZero (hb i hi))
  have hf : ∀ i : ℤ,
      Module.Flat (S.presheaf.stalk (f ((pullback.fst f g) x'))) (P.X i) := by
    intro i
    exact relative_flat_module_stalk f (G.X i) (hflat i) _ hRA
  have hK := CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat P hb hf
  have hC := pullback_stalk_tensor_flat g f x' hRA hRB hAC hBC
  exact ModuleCat.localizedComparison_isIso_of_kFlat_flat Q hK hC M

end AlgebraicGeometry
