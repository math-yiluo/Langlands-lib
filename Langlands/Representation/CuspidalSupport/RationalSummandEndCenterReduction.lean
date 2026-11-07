import Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeCommutative
import Langlands.Representation.CuspidalSupport.NormalHeckeCenter
import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterStatement
import Langlands.Representation.CuspidalSupport.RationalSummandEndNoetherianStatement
import Langlands.Representation.CuspidalSupport.RationalSummandCenterGroupAlgebraStatement
import Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement
import Langlands.Representation.CuspidalSupport.RationalInertiaLifting
import Langlands.Representation.CuspidalSupport.RationalPointCentralCharacter
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates
import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary

/-! Renard VI.4.4: the Theorem, the Corollary and the Proposition follow from the
Theorem of VI.4.1 and the finite-length clause of VI.3.2(ii), through the generic
results of `NormalHeckeCenter`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uG uX

namespace NormalHecke

section FiniteHom

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

/-- Maps between simple modules form a finite-dimensional space when the endomorphisms of the
source do. -/
theorem finiteDimensional_linearMap_of_isSimpleModule
    (S Q : Type*) [AddCommGroup S] [Module R S] [Module k S] [IsScalarTower k R S]
    [AddCommGroup Q] [Module R Q] [Module k Q] [IsScalarTower k R Q]
    [IsSimpleModule R S] [IsSimpleModule R Q] [FiniteDimensional k (S →ₗ[R] S)] :
    FiniteDimensional k (S →ₗ[R] Q) := by
  by_cases h : ∃ e : S →ₗ[R] Q, e ≠ 0
  · obtain ⟨e, he⟩ := h
    let e' := LinearEquiv.ofBijective e (LinearMap.bijective_of_ne_zero he)
    let φ : (S →ₗ[R] Q) →ₗ[k] (S →ₗ[R] S) :=
      { toFun := fun g => e'.symm.toLinearMap ∘ₗ g
        map_add' := fun g g' => LinearMap.ext fun x => map_add e'.symm (g x) (g' x)
        map_smul' := fun c g => LinearMap.ext fun x =>
          e'.symm.toLinearMap.map_smul_of_tower c (g x) }
    refine Module.Finite.of_injective φ fun g g' hg => LinearMap.ext fun x => ?_
    exact e'.symm.injective (LinearMap.congr_fun hg x)
  · push Not at h
    have : Subsingleton (S →ₗ[R] Q) := ⟨fun a b => (h a).trans (h b).symm⟩
    infer_instance

/-- Maps from a simple module `S` into a module of finite length form a finite-dimensional
space when the endomorphisms of `S` do. -/
theorem finiteDimensional_linearMap_of_isFiniteLength
    (S : Type*) [AddCommGroup S] [Module R S] [Module k S] [IsScalarTower k R S]
    [IsSimpleModule R S] [FiniteDimensional k (S →ₗ[R] S)]
    {M : Type*} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    ∀ [Module k M] [IsScalarTower k R M], FiniteDimensional k (S →ₗ[R] M) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    intro _ _
    have : Subsingleton (S →ₗ[R] M) := inferInstance
    infer_instance
  | @of_simple_quotient M _ _ N _ _ ih =>
    intro _ _
    have hQ := finiteDimensional_linearMap_of_isSimpleModule (k := k) (R := R) S (M ⧸ N)
    have hN : FiniteDimensional k (S →ₗ[R] N) := ih
    let q : (S →ₗ[R] M) →ₗ[k] (S →ₗ[R] M ⧸ N) :=
      { toFun := fun f => N.mkQ ∘ₗ f
        map_add' := fun f g => LinearMap.ext fun x => map_add N.mkQ (f x) (g x)
        map_smul' := fun c f => LinearMap.ext fun x => N.mkQ.map_smul_of_tower c (f x) }
    let i : (S →ₗ[R] N) →ₗ[k] (S →ₗ[R] M) :=
      { toFun := fun f => N.subtype ∘ₗ f
        map_add' := fun f g => LinearMap.ext fun x => rfl
        map_smul' := fun c f => LinearMap.ext fun x => rfl }
    have hker : LinearMap.ker q ≤ LinearMap.range i := by
      intro f hf
      have hf' : ∀ x, f x ∈ N := fun x => by
        have h1 := LinearMap.congr_fun (LinearMap.mem_ker.mp hf) x
        exact (Submodule.Quotient.mk_eq_zero N).mp h1
      exact ⟨LinearMap.codRestrict N f hf', LinearMap.ext fun x => rfl⟩
    have : FiniteDimensional k (LinearMap.ker q) := Submodule.finiteDimensional_of_le hker
    have h1 := LinearMap.rank_range_add_rank_ker q
    refine Module.rank_lt_aleph0_iff.mp ?_
    rw [← h1]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)

end FiniteHom

section Smooth

variable {H : Type uG} [Group H] [TopologicalSpace H]

/-- Maps from an irreducible smooth representation of countable dimension into a smooth
representation of finite length form a finite-dimensional space. -/
theorem finiteDimensional_hom_of_isFiniteLength (ρ B : SmoothRep.{0, uG, uV} ℂ H)
    [hρ : ρ.representation.IsIrreducible] (hrank : Module.rank ℂ ρ ≤ Cardinal.aleph0)
    (hB : IsFiniteLength (MonoidAlgebra ℂ H) B.representation.asModule) :
    FiniteDimensional ℂ (ρ ⟶ B) := by
  have : FiniteDimensional ℂ
      (ρ.representation.asModule →ₗ[MonoidAlgebra ℂ H] ρ.representation.asModule) := by
    have : FiniteDimensional ℂ (ρ.representation.IntertwiningMap ρ.representation) := by
      refine Module.Finite.of_surjective (LinearMap.toSpanSingleton ℂ _
        (Representation.IntertwiningMap.id ρ.representation)) fun f => ?_
      obtain ⟨c, hc, -⟩ := countableDimensionalSchur ρ.representation hrank hρ f
      exact ⟨c, hc.symm⟩
    exact Module.Finite.equiv
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ.representation ρ.representation)
  have := finiteDimensional_linearMap_of_isFiniteLength (k := ℂ) ρ.representation.asModule hB
  exact Module.Finite.equiv ((homLinearEquiv ρ B).trans
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _)).symm

/-- An irreducible subquotient of an irreducible smooth representation is isomorphic to it. -/
theorem nonempty_iso_of_isSubquotient {A D : SmoothRep.{0, uG, uV} ℂ H}
    (hA : A.IsIrreducible) (hD : D.IsIrreducible) (h : SmoothRep.IsSubquotient D A) :
    Nonempty (D ≅ A) := by
  have : A.representation.IsIrreducible := hA
  have : D.representation.IsIrreducible := hD
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp h
  have : Nontrivial D.representation.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) _
  obtain ⟨d, hd⟩ := exists_ne (0 : D.representation.asModule)
  obtain ⟨c, rfl⟩ := hq d
  have hi0 : SmoothRep.hom i ≠ 0 := fun h0 => by
    have hc : c = 0 := hi (by rw [h0, map_zero]; rfl)
    exact hd (by rw [hc, map_zero]; rfl)
  have hisurj := (Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom i)).resolve_right
    hi0
  let eCA := (SmoothRep.hom i).ofBijective ⟨hi, hisurj⟩
  let f := (SmoothRep.hom q).comp eCA.symm.toIntertwiningMap
  have hfsurj : Function.Surjective f := fun x => by
    obtain ⟨y, rfl⟩ := hq x
    exact ⟨eCA y, congrArg (SmoothRep.hom q) (eCA.symm_apply_apply y)⟩
  have hf0 : f ≠ 0 := fun h0 => by
    obtain ⟨y, hy⟩ := hfsurj (SmoothRep.hom q c)
    exact hd (by rw [← hy, h0]; rfl)
  have hfinj := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf0
  exact ⟨SmoothRep.mkIso (f.ofBijective ⟨hfinj, hfsurj⟩).symm⟩

/-- A homomorphism with open kernel from a topological group is continuous. -/
theorem continuous_of_isOpen_ker [IsTopologicalGroup H] {M : Type*} [Monoid M]
    [TopologicalSpace M] [ContinuousMul M] (ω : H →* M) (hω : IsOpen (ω.ker : Set H)) :
    Continuous ω := by
  refine continuous_of_continuousAt_one ω ?_
  refine (continuousAt_const (y := (1 : M))).congr ?_
  filter_upwards [hω.mem_nhds (one_mem ω.ker)] with x hx
  exact (MonoidHom.mem_ker.mp hx).symm

/-- Twisting commutes with the carrier lift. -/
def liftTwistIso (ω : H →* ℂˣ) (hω : IsOpen (ω.ker : Set H)) (π : SmoothRep.{0, uG, uV} ℂ H) :
    (SmoothRep.universeLiftFunctor.{uX, uG, uV} H).obj (π.twist ω hω) ≅
      ((SmoothRep.universeLiftFunctor.{uX, uG, uV} H).obj π).twist ω hω :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun _ => LinearMap.ext fun _ => rfl)

end Smooth

end NormalHecke

section Rational

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSummandEndCenterTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalSummandEndCenterTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The valuation of rational characters is a degree for the common norm kernel. -/
theorem isDegree_rationalValuation :
    NormalHecke.IsDegree (rationalCommonNormKernel G)
      (fun g => Additive.ofMul (rationalValuationImageProjection G g)) where
  map_mul x y := by rw [map_mul, ofMul_mul]
  eq_zero_iff g := by
    rw [ofMul_eq_zero, ← MonoidHom.mem_ker, rationalValuationImageProjection_ker]

/-- An irreducible smooth representation of the common norm kernel has countable dimension. -/
theorem rank_le_aleph0_of_rationalCommonNormKernel
    (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)) (hρ : ρ.IsIrreducible) :
    Module.rank ℂ ρ ≤ Cardinal.aleph0 := by
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  have : SecondCountableTopology (GroupScheme.rationalPoints G) :=
    (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
  have : SecondCountableTopology (rationalCommonNormKernel G) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact Whittaker.MirabolicRigidity.rank_le_aleph0 ρ.representation ρ.isSmooth hρ

/-- A character with open kernel containing the common norm kernel, as an unramified
character. -/
def rationalUnramifiedOfOpen (ω : GroupScheme.rationalPoints G →* ℂˣ)
    (hω : IsOpen (ω.ker : Set (GroupScheme.rationalPoints G)))
    (hωH : rationalCommonNormKernel G ≤ ω.ker) :
    unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul) :=
  ⟨{ ω with continuous_toFun := NormalHecke.continuous_of_isOpen_ker ω hω }, hωH⟩

variable {G}
variable {π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)}
variable {ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)}

/-- The twist group `T` in terms of the carrier lift of `π`. -/
theorem mem_rationalTwistGroup_iff (g : GroupScheme.rationalPoints G) :
    g ∈ (⨅ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
        (_ : Nonempty (rationalUnramifiedTwist G ω π ≅ π)), ω.val.toMonoidHom.ker) ↔
      ∀ (ω : GroupScheme.rationalPoints G →* ℂˣ)
        (hω : IsOpen (ω.ker : Set (GroupScheme.rationalPoints G))),
        rationalCommonNormKernel G ≤ ω.ker →
          Nonempty ((rationalInertiaBaseLift G π).twist ω hω ≅ rationalInertiaBaseLift G π) →
            ω g = 1 := by
  simp only [Subgroup.mem_iInf]
  constructor
  · rintro h ω hω hωH ⟨e⟩
    exact h (rationalUnramifiedOfOpen G ω hω hωH)
      ⟨(SmoothRep.fullyFaithfulUniverseLiftFunctor (G := GroupScheme.rationalPoints G)).preimageIso
        (NormalHecke.liftTwistIso ω hω π ≪≫ e)⟩
  · rintro h χ ⟨e⟩
    exact h χ.val.toMonoidHom (isOpen_rationalUnramifiedCharacter_ker G χ) χ.property
      ⟨(NormalHecke.liftTwistIso _ _ π).symm ≪≫
        (SmoothRep.universeLiftFunctor (GroupScheme.rationalPoints G)).mapIso e⟩

/-- With finite length of the restriction of `π`, the maps `ind ρ → π` form a
finite-dimensional space. -/
theorem finiteDimensional_rationalSummandHom (hρ : ρ.IsIrreducible)
    (hlen : IsFiniteLength (MonoidAlgebra ℂ (rationalCommonNormKernel G))
      (Representation.asModule (π.representation.comp (rationalCommonNormKernel G).subtype))) :
    FiniteDimensional ℂ
      (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π) := by
  have : ρ.representation.IsIrreducible := hρ
  have := NormalHecke.finiteDimensional_hom_of_isFiniteLength ρ
    (SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π)
    (rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ) hlen
  exact Module.Finite.equiv (NormalHecke.inducedLiftHomEquiv (rationalCommonNormKernel G) ρ
    (isOpen_rationalCommonNormKernel G) π).symm

/-- An injective map `ρ → π|_{⁰G}` gives a nonzero map `ind ρ → π`. -/
theorem nontrivial_rationalSummandHom (hρ : ρ.IsIrreducible)
    (j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π)
    (hj : Function.Injective (SmoothRep.hom j)) :
    Nontrivial
      (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π) := by
  have : ρ.representation.IsIrreducible := hρ
  let e := NormalHecke.inducedLiftHomEquiv (rationalCommonNormKernel G) ρ
    (isOpen_rationalCommonNormKernel G) π
  refine nontrivial_of_ne (e.symm j) 0 fun h => ?_
  have hj0 : j = 0 := by simpa using congrArg e h
  have : Nontrivial ρ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalCommonNormKernel G))
      ρ.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ)
  exact hv (hj (by rw [hj0, map_zero]; rfl))

variable (hπ : π.IsIrreducible)
include hπ

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
theorem isIrreducible_rationalInertiaBaseLift : (rationalInertiaBaseLift G π).IsIrreducible :=
  (SmoothRep.isIrreducible_universeLift_iff π).mpr hπ

/-- The carrier lift of an irreducible `π` lies in its own block. -/
theorem rationalInertiaBlockProperty_baseLift :
    rationalInertiaBlockProperty G (rationalInertiaBaseLift G π) (rationalInertiaBaseLift G π) :=
  fun _ hD hDA => by
    obtain ⟨e⟩ := NormalHecke.nonempty_iso_of_isSubquotient
      (isIrreducible_rationalInertiaBaseLift hπ) hD hDA
    exact IsRationalInertiaRelated.of_iso e.symm

/-- A twist of the carrier lift of an irreducible `π` by an unramified character lies in the
block of `π`. -/
theorem rationalInertiaBlockProperty_baseLift_twist (ω : GroupScheme.rationalPoints G →* ℂˣ)
    (hω : IsOpen (ω.ker : Set (GroupScheme.rationalPoints G)))
    (hωH : rationalCommonNormKernel G ≤ ω.ker) :
    rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      ((rationalInertiaBaseLift G π).twist ω hω) :=
  fun _ hD hDA => by
    have hirr : ((rationalInertiaBaseLift G π).twist ω hω).IsIrreducible :=
      (SmoothRep.isIrreducible_twist_iff ω hω _).mpr (isIrreducible_rationalInertiaBaseLift hπ)
    obtain ⟨e⟩ := NormalHecke.nonempty_iso_of_isSubquotient hirr hD hDA
    exact ⟨rationalUnramifiedOfOpen G ω hω hωH, ⟨e⟩⟩

variable (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
  (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ))
variable [hEqv : (preadditiveCoyonedaObj
  (⟨_, hmem⟩ : RationalInertiaBlock G (rationalInertiaBaseLift G π))).IsEquivalence]
include hmem hEqv

/-- Every map `ind ρ → π` is a multiple of any nonzero one under `End(ind ρ)`. -/
theorem rationalSummand_cyclic
    (φ : NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π)
    (hφ : φ ≠ 0)
    (ψ : NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π) :
    ∃ α : End (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ), α ≫ φ = ψ := by
  have : (rationalInertiaBaseLift G π).representation.IsIrreducible :=
    isIrreducible_rationalInertiaBaseLift hπ
  have hsurj : Function.Surjective (SmoothRep.hom φ) := by
    refine (Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom φ)).resolve_right
      fun h0 => hφ ?_
    rw [← SmoothRep.ofHom_hom φ, h0]
    rfl
  let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) := ⟨_, hmem⟩
  let Q : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
    ⟨_, rationalInertiaBlockProperty_baseLift hπ⟩
  let φ' : P ⟶ Q := ObjectProperty.homMk φ
  have : Epi φ' := (rationalInertiaBlock_epi_iff_surjective G _ φ').mpr hsurj
  have h1 := (ModuleCat.epi_iff_surjective ((preadditiveCoyonedaObj P).map φ')).mp inferInstance
  obtain ⟨x, hx⟩ := h1 (ObjectProperty.homMk ψ : P ⟶ Q)
  exact ⟨x.hom, congrArg (fun f : P ⟶ Q => f.hom) hx⟩

/-- An equivariant identification of the maps into a twist with the maps into `π` gives an
isomorphism of the twist with `π`. -/
theorem rationalSummand_twistIso (ω : GroupScheme.rationalPoints G →* ℂˣ)
    (hω : IsOpen (ω.ker : Set (GroupScheme.rationalPoints G)))
    (hωH : rationalCommonNormKernel G ≤ ω.ker)
    (Ψ : (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶
        (rationalInertiaBaseLift G π).twist ω hω) ≃ₗ[ℂ]
      (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π))
    (hΨ : ∀ (α : End (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ)) φ,
      Ψ (α ≫ φ) = α ≫ Ψ φ) :
    Nonempty ((rationalInertiaBaseLift G π).twist ω hω ≅ rationalInertiaBaseLift G π) := by
  let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) := ⟨_, hmem⟩
  let X : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
    ⟨_, rationalInertiaBlockProperty_baseLift_twist hπ ω hω hωH⟩
  let Y : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
    ⟨_, rationalInertiaBlockProperty_baseLift hπ⟩
  let ΨP : (P ⟶ X) ≃ₗ[(End P)ᵐᵒᵖ] (P ⟶ Y) :=
    { toFun := fun f => ObjectProperty.homMk (Ψ f.hom)
      invFun := fun f => ObjectProperty.homMk (Ψ.symm f.hom)
      map_add' := fun f g => ObjectProperty.hom_ext _ (map_add Ψ f.hom g.hom)
      map_smul' := fun a f => ObjectProperty.hom_ext _ (hΨ a.unop.hom f.hom)
      left_inv := fun f => ObjectProperty.hom_ext _ (Ψ.symm_apply_apply f.hom)
      right_inv := fun f => ObjectProperty.hom_ext _ (Ψ.apply_symm_apply f.hom) }
  let e : (preadditiveCoyonedaObj P).obj X ≅ (preadditiveCoyonedaObj P).obj Y :=
    ΨP.toModuleIso
  exact ⟨(rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)).ι.mapIso
    ((preadditiveCoyonedaObj P).preimageIso e)⟩

end Rational

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- Renard VI.4.4, Theorem, from the Theorem of VI.4.1 and the finite-length clause of
VI.3.2(ii), with the same quantifiers, premises and universes. -/
theorem rationalSummandEndCenter_of_homEquivalence
    (hEq : RationalSummandHomEquivalenceStatement.{uF, uV})
    (hFin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}) :
    RationalSummandEndCenterStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj T I f
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨hmem, hEqv⟩ := hEq F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ j hj
  have hlen := (hFin F G hG π hπ).2.1
  classical
  have : ρ.representation.IsIrreducible := hρ
  have := finiteDimensional_rationalSummandHom hρ hlen
  have := nontrivial_rationalSummandHom hρ j hj
  have hH := isOpen_rationalCommonNormKernel G
  have hrank := rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ
  have hcyc := rationalSummand_cyclic hπ hmem
  refine ⟨fun α => (NormalHecke.mem_center_iff_endValue ρ hH (isDegree_rationalValuation G)
    hrank _ hcyc (rationalSummand_twistIso hπ hmem) (fun g => mem_rationalTwistGroup_iff g)
    α).trans ⟨fun h w g hg => LinearMap.congr_fun (h g hg) w,
      fun h g hg => LinearMap.ext fun w => h w g hg⟩, ?_⟩
  let e := NormalHecke.inducedLiftHomEquiv (rationalCommonNormKernel G) ρ hH π
  have : FiniteDimensional ℂ (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π) :=
    Module.Finite.equiv e
  refine ⟨Module.finrank ℂ (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π),
    (Module.finrank_eq_rank ℂ _).symm, ?_⟩
  rw [← e.finrank_eq]
  exact NormalHecke.exists_basis_center ρ hH (isDegree_rationalValuation G) hrank _ hcyc

/-- Renard VI.4.4, Corollary, from the Theorem of VI.4.1 and the finite-length clause of
VI.3.2(ii), with the same quantifiers, premises and universes. -/
theorem rationalSummandEndNoetherian_of_homEquivalence
    (hEq : RationalSummandHomEquivalenceStatement.{uF, uV})
    (hFin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}) :
    RationalSummandEndNoetherianStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj I
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨hmem, hEqv⟩ := hEq F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ j hj
  have hlen := (hFin F G hG π hπ).2.1
  classical
  have : ρ.representation.IsIrreducible := hρ
  have := finiteDimensional_rationalSummandHom hρ hlen
  have := nontrivial_rationalSummandHom hρ j hj
  have : Module.Finite ℤ (Additive (rationalDiscreteValuationImage G)) :=
    Module.Finite.of_basis (rationalReductiveValuationBasis G hG)
  exact NormalHecke.isNoetherianRing_end ρ (isOpen_rationalCommonNormKernel G)
    (isDegree_rationalValuation G) (rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ) _
    (rationalSummand_cyclic hπ hmem)

/-- Renard VI.4.4, Proposition, from the Theorem of VI.4.1 and the finite-length clause of
VI.3.2(ii), with the same quantifiers, premises and universes. -/
theorem rationalSummandCenterGroupAlgebra_of_homEquivalence
    (hEq : RationalSummandHomEquivalenceStatement.{uF, uV})
    (hFin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}) :
    RationalSummandCenterGroupAlgebraStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj T I f
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨hmem, hEqv⟩ := hEq F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ j hj
  have hlen := (hFin F G hG π hπ).2.1
  classical
  have : ρ.representation.IsIrreducible := hρ
  have := finiteDimensional_rationalSummandHom hρ hlen
  have := nontrivial_rationalSummandHom hρ j hj
  obtain ⟨e, he⟩ := NormalHecke.exists_algEquiv_center_quotient ρ
    (isOpen_rationalCommonNormKernel G) (isDegree_rationalValuation G)
    (rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ) _ (rationalSummand_cyclic hπ hmem)
    (rationalSummand_twistIso hπ hmem) (fun g => mem_rationalTwistGroup_iff g)
  refine ⟨e, fun t => ?_⟩
  intro ψ
  exact ⟨fun w g hg => LinearMap.congr_fun ((he t).1 g hg) w,
    fun ω φ => (he t).2 ω.val.toMonoidHom (isOpen_rationalUnramifiedCharacter_ker G ω)
      ω.property φ⟩

end Langlands.CuspidalSupport
