import Langlands.GroupScheme.Rational.CharactersStatement
import Langlands.GroupScheme.Rational.CharacterUnits
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk

/-! # Finiteness of the rational character lattice

Over a field `k`, the rational characters of a connected reductive group `G` form a free
`ℤ`-module of finite rank. Only smoothness, affineness and connectedness of `G` are used: the
coordinate algebra `O(G)` is then a finitely generated `k`-domain, and characters give
`k`-linearly independent units of `O(G)` (`CharacterUnits`), so the commutative algebra of
`CharacterLatticeAlgebra` applies in the fraction field of `O(G)`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

namespace CharacterLatticeProof

/-- `Γ(Spec k, ⊤)` is a domain. -/
instance isDomain_sections_spec (k : Type u) [Field k] :
    IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
  MulEquiv.isDomain k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

/-- `Γ(Spec k, ⊤)` is integrally closed. -/
instance isIntegrallyClosed_sections_spec (k : Type u) [Field k] :
    IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
  IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm

/-- A connected, locally noetherian scheme smooth over a field is integral: its stalks are
domains, so its irreducible components are open and closed, and connectedness leaves only one. -/
theorem isIntegral_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [IsLocallyNoetherian X] [ConnectedSpace X] :
    IsIntegral X := by
  have hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x =>
    (Smooth.isDomain_and_isIntegrallyClosed_stalk f x).1
  have : IrreducibleSpace X := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hopen := (isOpen_irreducibleComponent_of_isDomain_stalk hdom x).1
    have hclosed := isClosed_of_mem_irreducibleComponents _
      (irreducibleComponent_mem_irreducibleComponents x)
    have huniv : irreducibleComponent x = Set.univ :=
      IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x, mem_irreducibleComponent⟩
    rw [irreducibleSpace_def, Set.top_eq_univ, ← huniv]
    exact isIrreducible_irreducibleComponent
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := hdom x
    infer_instance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom]

/-- The coordinate algebra of a smooth connected affine group over a field is a domain. -/
theorem isDomain_coord [Smooth G.X.hom] [ConnectedSpace G.X.left] :
    IsDomain (CharacterUnits.Coord G) := by
  set D := CharacterUnits.Coord G
  have hsm : Smooth ((algSpec (CommRingCat.of k)).obj (op D)).hom := by
    have : IsIso (Lie.coordinateIso G).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (Lie.coordinateIso G).hom))
    have h : Smooth ((Lie.coordinateIso G).hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of k) D))) at hsm
  have : Algebra.FiniteType (CommRingCat.of k) D := Lie.coordinateAlgebraFiniteType G
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing (CommRingCat.of k) D
  have : IsNoetherianRing (CommRingCat.of D) := inferInstanceAs (IsNoetherianRing D)
  have e : Spec (CommRingCat.of D) ≅ G.X.left := (Over.forget _).mapIso (Lie.coordinateIso G)
  have : ConnectedSpace (Spec (CommRingCat.of D)) :=
    (Scheme.homeoOfIso e).connectedSpace_iff.mpr inferInstance
  have := isIntegral_of_smooth k (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of k) D)))
  exact (affine_isIntegral_iff (CommRingCat.of D)).mp this

end CharacterLatticeProof

open CharacterLatticeProof CharacterUnits CharacterLattice in
/-- Over every field `k`, the rational characters of a connected reductive group form a free
`ℤ`-module of finite rank. -/
theorem rationalCharacterLattice : RationalCharacterLatticeStatement.{u} := by
  classical
  intro k _ G hG
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have := isDomain_coord G
  let K : Type u := CommRingCat.of k
  let _ : Field K := inferInstanceAs (Field k)
  set D := Coord G
  set L := FractionRing D
  let w : Multiplicative (rationalCharacters G) →* L :=
    { toFun := fun χ => algebraMap D L (unit χ.toAdd : D)
      map_one' := by simp [unit_zero]
      map_mul' := fun a b => by simp [toAdd_mul, unit_add] }
  have hw : LinearIndependent K (wa w) := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom K D L) :=
      IsFractionRing.injective D L
    exact (linearIndependent_unit (G := G)).map' (IsScalarTower.toAlgHom K D L).toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨s, hs⟩ := (Lie.coordinateAlgebraFiniteType G).out
  refine free_and_finite (k := K) w hw (s.image (algebraMap D L)) fun χ => ?_
  change algebraMap D L (unit χ : D) ∈ _
  rw [Finset.coe_image, ← IsScalarTower.coe_toAlgHom' K D L, Algebra.adjoin_image]
  exact Subalgebra.mem_map.mpr ⟨_, hs ▸ Algebra.mem_top, rfl⟩

end Langlands.GroupScheme
