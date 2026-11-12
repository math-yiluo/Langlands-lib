import Langlands.GroupScheme.Rational.EvenChainGaloisDataStatement
import Langlands.GroupScheme.Rational.SteinbergRationalGaloisTransport

/-! # Galois-stable even-chain data when simple-root orbits are orthogonal -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace SplitPinning

variable {F : Type u} [Field F]
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]

/-- The empty family of even paths. Its remaining roots are all simple roots. -/
def emptyEvenChainData (p : SplitPinning H) : p.EvenChainData PEmpty where
  half := PEmpty.elim
  path := fun c => PEmpty.elim c
  isPathComponent := fun c => PEmpty.elim c
  disjoint := fun c => PEmpty.elim c
  modified := PEmpty.elim
  modified_a := fun c => PEmpty.elim c
  modified_b := fun c => PEmpty.elim c
  nAlpha_mem := fun c => PEmpty.elim c

/-- Forget the vacuous exclusion of middle vertices of the empty path family. -/
def emptyEvenChainRestEquiv (p : SplitPinning H) :
    (emptyEvenChainData p).Rest ≃ p.base.support where
  toFun := Subtype.val
  invFun := fun a => ⟨a, fun c => PEmpty.elim c⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem emptyEvenChainData_isMiddleOut (p : SplitPinning H) {q : ℕ}
    (e : Fin q ≃ (emptyEvenChainData p).Rest) :
    (emptyEvenChainData p).IsMiddleOut e :=
  fun c => PEmpty.elim c

/-- Order the unmerged roots of the empty path family in actual orbit blocks. -/
def emptyEvenChainOrdering (p : SplitPinning H) {Γ : Type u} [Group Γ]
    (ρ : Γ →* Equiv.Perm p.base.support) :
    Fin (p.simpleOrbitBlocks ρ).flatten.length ≃ (emptyEvenChainData p).Rest :=
  (p.simpleOrbitOrdering ρ).trans (emptyEvenChainRestEquiv p).symm

end SplitPinning

section Galois

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

namespace GaloisCompatiblePinningData

variable {k K G}

variable (D : GaloisCompatiblePinningData k K G)

/-- The canonical rational Steinberg factor at a simple root. -/
def rationalRootFactor (a : D.pinning.base.support) (c : K) :
    rationalPoints (GaloisPointComparison.baseChanged k K G) :=
  (D.rootMaps a).toRootParametrization.rationalPoint c *
    (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps a).point

/-- The canonical rational product in simple-root orbit order, with coordinates
indexed by the simple roots themselves. -/
def rationalOrbitProduct (d : D.pinning.base.support → K) :
    rationalPoints (GaloisPointComparison.baseChanged k K G) :=
  ((D.pinning.simpleOrbitBlocks D.action).flatten.map (fun a =>
    D.rationalRootFactor a (d a))).prod

/-- At rational points, factors belonging to distinct orthogonal simple roots commute. -/
theorem commute_rationalRootFactors (a b : D.pinning.base.support)
    (hab : a ≠ b) (ho : D.pinning.rootDatum.IsOrthogonal a b) (c d : K) :
    Commute (D.rationalRootFactor a c) (D.rationalRootFactor b d) := by
  have ht : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K)))) =
      𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := toUnit_unique _ _
  simpa only [rationalRootFactor, SplitPinning.RootParametrization.rationalPoint,
    SplitPinning.NormalizedRootParametrization.toRootParametrization,
    SplitPinning.RootParametrization.point, SplitPinning.NormalizedRootParametrization.point,
    ht, Category.id_comp] using
    SplitPinning.commute_canonicalRootFactors D.rootMaps a b hab ho
      (Over.mk (𝟙 (Spec (CommRingCat.of K))))
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv d)

/-- The root coordinate and the canonical representative transport together. -/
theorem rationalRootFactor_rationalConjugate
    (σ : K ≃ₐ[k] K) (a : D.pinning.base.support) (c : K) :
    GaloisPointComparison.rationalConjugate k K G σ (D.rationalRootFactor a c) =
      D.rationalRootFactor (D.action σ a) (σ c) := by
  unfold rationalRootFactor
  exact (map_mul (GaloisPointComparison.rationalConjugate k K G σ) _ _).trans
    (congrArg₂ (fun x y => x * y)
      (SplitPinning.RootMapsGaloisCompatible.rationalPoints k K G
        D.rootMaps D.action D.rootMaps_compatible σ a c)
      (SplitPinning.canonicalSimpleReflectionRepresentatives_rationalConjugate
        k K D.inclusion D.pinning D.torusIso D.inclusion_eq D.rootMaps
        D.action D.action_root
        (SplitPinning.RootMapsGaloisCompatible.unitPoints k K
          D.pinning D.rootMaps D.action D.rootMaps_compatible) σ a))

/-- Galois transport permutes factors inside each orthogonal orbit block and
conjugates and permutes their coordinates. -/
theorem rationalOrbitProduct_rationalConjugate
    (horth : D.pinning.OrthogonalSimpleOrbits D.action)
    (σ : K ≃ₐ[k] K) (d : D.pinning.base.support → K) :
    GaloisPointComparison.rationalConjugate k K G σ (D.rationalOrbitProduct d) =
      D.rationalOrbitProduct
        (PolynomialGalois.rootCoordinateConjugate k K D.action σ d) := by
  let f := fun a : D.pinning.base.support =>
    D.rationalRootFactor a (σ (d ((D.action σ).symm a)))
  have hf (a : D.pinning.base.support) :
      GaloisPointComparison.rationalConjugate k K G σ (D.rationalRootFactor a (d a)) =
        f (D.action σ a) := by
    simpa only [f, Equiv.symm_apply_apply] using
      D.rationalRootFactor_rationalConjugate σ a (d a)
  unfold rationalOrbitProduct
  rw [List.map_flatten, List.prod_flatten, map_list_prod, List.map_map,
    List.map_flatten, List.prod_flatten]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro l hl
  dsimp only [Function.comp_def]
  rw [map_list_prod, List.map_map]
  have hcomm : (l.map f).Pairwise Commute := by
    rw [List.pairwise_map]
    exact (D.pinning.simpleOrbitBlocks_pairwise D.action horth l hl).imp
      (fun h => D.commute_rationalRootFactors _ _ h.1 h.2 _ _)
  simpa only [List.map_map, Function.comp_def, hf,
    PolynomialGalois.rootCoordinateConjugate] using
    (((D.pinning.simpleOrbitBlocks_invariant D.action σ l hl).map f).symm.prod_eq'
      hcomm).symm

/-- With no selected paths, a pattern product is exactly the rational orbit product. -/
theorem emptyEvenChain_patternProduct (ε : PEmpty → Bool) (s : PEmpty → K)
    (t : PEmpty → Kˣ)
    (d : Fin (D.pinning.simpleOrbitBlocks D.action).flatten.length → K) :
    (SplitPinning.emptyEvenChainData D.pinning).patternProduct D.rootMaps
        (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps)
        (Equiv.equivOfIsEmpty (Fin 0) PEmpty)
        (D.pinning.emptyEvenChainOrdering D.action) ε s t d =
      D.rationalOrbitProduct
        (fun a => d ((D.pinning.simpleOrbitOrdering D.action).symm a)) := by
  unfold SplitPinning.EvenChainData.patternProduct rationalOrbitProduct
  let f := fun a : D.pinning.base.support =>
    D.rationalRootFactor a (d ((D.pinning.simpleOrbitOrdering D.action).symm a))
  have hlist := congrArg (fun l : List D.pinning.base.support => (l.map f).prod)
    (D.pinning.simpleOrbitBlocks_flatten_eq D.action)
  change _ = ((D.pinning.simpleOrbitBlocks D.action).flatten.map f).prod
  rw [hlist, List.map_ofFn]
  dsimp only [f]
  simp only [rationalRootFactor, List.ofFn_zero, List.prod_nil, one_mul,
    SplitPinning.emptyEvenChainOrdering, Equiv.trans_apply,
    SplitPinning.emptyEvenChainRestEquiv, Equiv.coe_fn_symm_mk,
    Function.comp_def, Equiv.symm_apply_apply]

/-- The pattern set for the empty path family is stable when all simple-root
orbits are orthogonal. -/
theorem emptyEvenChain_patternSet_stable
    (horth : D.pinning.OrthogonalSimpleOrbits D.action)
    (σ : K ≃ₐ[k] K) (g : rationalPoints (GaloisPointComparison.baseChanged k K G))
    (hg : g ∈ (SplitPinning.emptyEvenChainData D.pinning).patternSet D.rootMaps
      (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps)
      (Equiv.equivOfIsEmpty (Fin 0) PEmpty)
      (D.pinning.emptyEvenChainOrdering D.action)) :
    GaloisPointComparison.rationalConjugate k K G σ g ∈
      (SplitPinning.emptyEvenChainData D.pinning).patternSet D.rootMaps
        (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps)
        (Equiv.equivOfIsEmpty (Fin 0) PEmpty)
        (D.pinning.emptyEvenChainOrdering D.action) := by
  obtain ⟨ε, s, t, d, rfl⟩ := hg
  refine ⟨ε, s, t, fun j => σ (d ((D.pinning.simpleOrbitOrdering D.action).symm
    ((D.action σ).symm (D.pinning.simpleOrbitOrdering D.action j)))), ?_⟩
  rw [D.emptyEvenChain_patternProduct,
    D.rationalOrbitProduct_rationalConjugate horth,
    D.emptyEvenChain_patternProduct]
  congr 1
  funext a
  simp only [PolynomialGalois.rootCoordinateConjugate, Equiv.apply_symm_apply]

/-- The even-chain existence conclusion for orthogonal simple-root orbits.
No selected path is needed in this case. -/
theorem exists_evenChainGaloisData_of_orthogonal
    (horth : D.pinning.OrthogonalSimpleOrbits D.action) :
    ∃ (J : Type u) (_ : Fintype J) (C : D.pinning.EvenChainData J) (r q : ℕ)
      (o : Fin r ≃ J) (e : Fin q ≃ C.Rest),
      C.IsMiddleOut e ∧
        ∀ (σ : K ≃ₐ[k] K) (g : rationalPoints (GaloisPointComparison.baseChanged k K G)),
          g ∈ C.patternSet D.rootMaps
              (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps) o e →
            GaloisPointComparison.rationalConjugate k K G σ g ∈ C.patternSet D.rootMaps
              (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps) o e := by
  refine ⟨PEmpty, inferInstance, SplitPinning.emptyEvenChainData D.pinning, 0,
    (D.pinning.simpleOrbitBlocks D.action).flatten.length,
    Equiv.equivOfIsEmpty (Fin 0) PEmpty, D.pinning.emptyEvenChainOrdering D.action,
    D.pinning.emptyEvenChainData_isMiddleOut _, ?_⟩
  exact D.emptyEvenChain_patternSet_stable horth

end GaloisCompatiblePinningData

end Galois

end Langlands.GroupScheme
