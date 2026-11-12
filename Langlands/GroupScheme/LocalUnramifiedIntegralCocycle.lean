import Langlands.GroupScheme.IntegralGaloisCocycle
import Langlands.GroupScheme.IntegralModel.GenericCoordinates
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.Galois.Local.SeparableUnramifiedProof
import Langlands.Galois.Local.SeparableUnramifiedFiniteArithmetic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (L : Type u) [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- Points of the generic group with values in a `K`-algebra `L` are points of the model with
values in `L`, multiplicatively: the specified generic isomorphism followed by the pullback
adjunction. -/
def modelPointEquiv :
    G.affinePoints (CommAlgCat.of K L) ≃* M.group.affinePoints (CommAlgCat.of R L) :=
  (MonoidHom.toMulEquiv (G.affinePointsTarget M.genericIso.inv (CommAlgCat.of K L))
      (M.genericFibre.affinePointsTarget M.genericIso.hom (CommAlgCat.of K L))
      (MonoidHom.ext fun x => by
        change (x ≫ ((Grp.forget _).mapIso M.genericIso).inv) ≫
          ((Grp.forget _).mapIso M.genericIso).hom = x
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (MonoidHom.ext fun x => by
        change (x ≫ ((Grp.forget _).mapIso M.genericIso).hom) ≫
          ((Grp.forget _).mapIso M.genericIso).inv = x
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])).trans
    (affinePointsBaseChangeMulEquiv R K L M.group).symm

theorem modelPointEquiv_left (p : G.affinePoints (CommAlgCat.of K L)) :
    (M.modelPointEquiv L p).left =
      (p.left ≫ M.genericIso.inv.hom.hom.left) ≫
        pullback.fst M.group.X.hom (Spec.algebraMap R K) := by
  change ((affinePointsBaseChangeMulEquiv R K L M.group).symm
    (p ≫ M.genericIso.inv.hom.hom)).left = _
  rw [affinePointsBaseChangeMulEquiv_symm_left]
  rfl

/-- The multiplicative comparison has the published generic-model point correspondence as its
underlying map. -/
theorem modelPointEquiv_eq_genericModelPointEquiv (p : G.affinePoints (CommAlgCat.of K L)) :
    (M.modelPointEquiv L p : RingPoint R M.group.X L) = M.genericModelPointEquiv L p := by
  apply Over.OverMorphism.ext
  rw [genericModelPointEquiv_left]
  exact M.modelPointEquiv_left L p

/-- The comparison intertwines a change of `K`-algebra coefficients with the same change of
coefficients regarded over `R`. -/
theorem modelPointEquiv_affinePointMap (φ : L →ₐ[K] L)
    (p : G.affinePoints (CommAlgCat.of K L)) :
    M.modelPointEquiv L (G.affinePointMap (CommAlgCat.ofHom φ) p) =
      M.group.affinePointMap (CommAlgCat.ofHom (φ.restrictScalars R))
        (M.modelPointEquiv L p) := by
  apply Over.OverMorphism.ext
  rw [modelPointEquiv_left, affinePointMap_apply, affinePointMap_apply, Over.comp_left,
    Over.comp_left, modelPointEquiv_left]
  simp only [Category.assoc]
  rfl

/-- A point of the generic group with values in a `K`-algebra `L` has integral coordinates for the
model `M` when every regular function of the model takes an `R`-integral value at it. -/
def HasIntegralCoordinates (p : G.affinePoints (CommAlgCat.of K L)) : Prop :=
  ∀ a : AffineCoordinateRing R M.group.X,
    IsIntegral R (G.affinePointEvaluation (CommAlgCat.of K L) p (M.genericCoordinate a))

section Lift

variable [IsAffine M.group.X.left] (T : Subalgebra R L)

/-- A point of the generic group whose generic model coordinates lie in a subalgebra `T` of the
values is the image of a model point with values in `T`. -/
theorem exists_affinePointMap_eq_of_mem (p : G.affinePoints (CommAlgCat.of K L))
    (hp : ∀ a : AffineCoordinateRing R M.group.X,
      G.affinePointEvaluation (CommAlgCat.of K L) p (M.genericCoordinate a) ∈ T) :
    ∃ x : M.group.affinePoints (CommAlgCat.of R T),
      M.group.affinePointMap (CommAlgCat.ofHom T.val) x = M.modelPointEquiv L p := by
  have hq : M.genericModelPointEquiv L p ∈
      Set.range (RingPoint.changeRing (X := M.group.X) T.val) := by
    rw [mem_range_changeRing_subalgebra_iff]
    intro a
    rw [genericModelPointEquiv_evaluation]
    exact hp a
  obtain ⟨x, hx⟩ := hq
  exact ⟨x, hx.trans (M.modelPointEquiv_eq_genericModelPointEquiv L p).symm⟩

/-- Conversely, the image of a model point with values in `T` has its generic model coordinates
in `T`. -/
theorem mem_of_affinePointMap_eq (p : G.affinePoints (CommAlgCat.of K L))
    (x : M.group.affinePoints (CommAlgCat.of R T))
    (hx : M.group.affinePointMap (CommAlgCat.ofHom T.val) x = M.modelPointEquiv L p)
    (a : AffineCoordinateRing R M.group.X) :
    G.affinePointEvaluation (CommAlgCat.of K L) p (M.genericCoordinate a) ∈ T := by
  rw [← genericModelPointEquiv_evaluation, ← M.modelPointEquiv_eq_genericModelPointEquiv L p]
  exact (mem_range_changeRing_subalgebra_iff R M.group.X L T _).mp ⟨x, hx⟩ a

end Lift

section GaloisSubalgebra

variable (T : Subalgebra R L) {Γ : Type u} [Group Γ]
  (act : Γ →* (L ≃ₐ[K] L)) (ρ : Γ →* (T ≃ₐ[R] T))

/-- Model points with values in `T`, inside model points with values in `L`. -/
abbrev subalgebraPointMap :
    M.group.affinePoints (CommAlgCat.of R T) →* M.group.affinePoints (CommAlgCat.of R L) :=
  M.group.affinePointMap (CommAlgCat.ofHom T.val)

omit [Algebra K L] [IsScalarTower R K L] in
theorem subalgebraPointMap_injective [IsAffine M.group.X.left] :
    Function.Injective (M.subalgebraPointMap L T) := by
  intro x y h
  apply M.group.affinePointEvaluation_injective
  funext a
  apply Subtype.val_injective
  have h' := congrArg (fun z => M.group.affinePointEvaluation (CommAlgCat.of R L) z a) h
  simp only [subalgebraPointMap] at h'
  rw [affinePointEvaluation_map, affinePointEvaluation_map] at h'
  exact h'

/-- If automorphisms of `T` are restrictions of automorphisms of `L`, the inclusion of `T`-valued
model points intertwines the two actions. -/
theorem subalgebraPointMap_conjugate (hρ : ∀ (g : Γ) (x : T), ((ρ g x : T) : L) = act g x)
    (g : Γ) (x : M.group.affinePoints (CommAlgCat.of R T)) :
    M.subalgebraPointMap L T (GaloisRingCover.conjugate M.group (ρ g) x) =
      M.group.affinePointMap (CommAlgCat.ofHom ((act g).toAlgHom.restrictScalars R))
        (M.subalgebraPointMap L T x) := by
  simp only [subalgebraPointMap, GaloisRingCover.conjugate]
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← affinePointMap_comp,
    ← affinePointMap_comp]
  congr 2
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro y
  exact hρ g y

/-- **Integral cocycle vanishing for model points.** Let `R` be complete for a maximal ideal `I`
with finite residue ring, and let `M` be a smooth model with connected special fibre. Let `T` be
a local `R`-subalgebra of `L`, finite and free over `R`, and let a finite group `Γ` act on `L` by
`K`-algebra automorphisms that restrict to `R`-algebra automorphisms of `T`, with `|Γ|` the rank
of `T` and `Γ` faithful on the residue field of `T`. Then every crossed homomorphism
`Γ → G(L)` whose values have generic model coordinates in `T` is the coboundary of a point
whose generic model coordinates lie in `T`. -/
theorem exists_integral_coboundary (I : Ideal R) [I.IsMaximal] [Finite (R ⧸ I)]
    [IsAdicComplete I R] (hM : M.IsSmooth)
    (hconn : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj M.group).X.left)
    [IsLocalRing T] [Module.Free R T] [Module.Finite R T] [Finite Γ]
    (hρ : ∀ (g : Γ) (x : T), ((ρ g x : T) : L) = act g x)
    (hcard : Nat.card Γ = Module.finrank R T)
    (hfaithful : ∀ g : Γ,
      (∀ x : T, IsLocalRing.residue T (ρ g x) = IsLocalRing.residue T x) → g = 1)
    (c : Γ → G.affinePoints (CommAlgCat.of K L))
    (hc : ∀ g h, c (g * h) = c g * G.affinePointMap (CommAlgCat.ofHom (act g).toAlgHom) (c h))
    (hint : ∀ g (a : AffineCoordinateRing R M.group.X),
      G.affinePointEvaluation (CommAlgCat.of K L) (c g) (M.genericCoordinate a) ∈ T) :
    ∃ f : G.affinePoints (CommAlgCat.of K L),
      (∀ a : AffineCoordinateRing R M.group.X,
        G.affinePointEvaluation (CommAlgCat.of K L) f (M.genericCoordinate a) ∈ T) ∧
      ∀ g, c g = f * (G.affinePointMap (CommAlgCat.ofHom (act g).toAlgHom) f)⁻¹ := by
  have : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  have : Smooth M.group.X.hom := hM
  have hlift : ∀ g, ∃ x : M.group.affinePoints (CommAlgCat.of R T),
      M.subalgebraPointMap L T x = M.modelPointEquiv L (c g) := fun g =>
    M.exists_affinePointMap_eq_of_mem L T (c g) (hint g)
  choose c' hc' using hlift
  have hconj : ∀ (g : Γ) (p : G.affinePoints (CommAlgCat.of K L)),
      M.modelPointEquiv L (G.affinePointMap (CommAlgCat.ofHom (act g).toAlgHom) p) =
        M.group.affinePointMap (CommAlgCat.ofHom ((act g).toAlgHom.restrictScalars R))
          (M.modelPointEquiv L p) := fun g p =>
    M.modelPointEquiv_affinePointMap L (act g).toAlgHom p
  have hcross : GaloisRingCover.IsCrossed ρ M.group c' := by
    intro g h
    apply M.subalgebraPointMap_injective L T
    rw [map_mul, M.subalgebraPointMap_conjugate L T act ρ hρ, hc', hc', hc', hc g h, map_mul,
      hconj]
  obtain ⟨f', hf'⟩ := integralGaloisCocycleVanishing R I M.group hconn T Γ ρ hcard hfaithful c'
    hcross
  obtain ⟨f, hf⟩ : ∃ f, M.modelPointEquiv L f = M.subalgebraPointMap L T f' :=
    ⟨_, MulEquiv.apply_symm_apply _ _⟩
  refine ⟨f, fun a => M.mem_of_affinePointMap_eq L T f f' hf.symm a, fun g => ?_⟩
  have h₁ : c' g * GaloisRingCover.conjugate M.group (ρ g) f' = f' :=
    eq_mul_inv_iff_mul_eq.mp (hf' g)
  have h₂ := congrArg (M.subalgebraPointMap L T) h₁
  rw [map_mul, hc' g, M.subalgebraPointMap_conjugate L T act ρ hρ, ← hf, ← hconj g f,
    ← map_mul] at h₂
  exact eq_mul_inv_iff_mul_eq.mpr ((M.modelPointEquiv L).injective h₂)

end GaloisSubalgebra

end IntegralModel

namespace LocalUnramified

open ValuativeRel IsLocalRing LocalGalois LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E]

/-- The ring of integers of `E`, as the integral closure of `𝒪[F]` in `E`. -/
abbrev integers : Subalgebra 𝒪[F] E := integralClosure 𝒪[F] E

instance : IsFractionRing (integers F E) E :=
  integralClosure.isFractionRing_of_finite_extension F E

private instance torsionFree : Module.IsTorsionFree 𝒪[F] E :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    ((algebraMap F E).injective.comp Subtype.val_injective)

instance : Module.Finite 𝒪[F] (integers F E) :=
  IsIntegralClosure.finite 𝒪[F] F E (integers F E)

instance : Module.Free 𝒪[F] (integers F E) :=
  IsIntegralClosure.module_free 𝒪[F] F E (integers F E)

theorem finrank_integers : Module.finrank 𝒪[F] (integers F E) = Module.finrank F E :=
  IsIntegralClosure.rank 𝒪[F] F E (integers F E)

section Spectral

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F
local instance : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

omit [FiniteDimensional F E] in
/-- Integrality over `𝒪[F]` is integrality over the integer ring of the normed structure. -/
theorem isIntegral_iff_baseIntegers (x : E) :
    IsIntegral 𝒪[F] x ↔ IsIntegral (baseIntegers F) x := by
  let e : (NormedField.valuation (K := F)).integer ≃+* 𝒪[F] :=
    RingEquiv.subringCongr (localNormedField_integer F)
  constructor
  · intro hx
    exact IsIntegral.map_of_comp_eq (S := E) (U := E) e.symm.toRingHom (RingHom.id E)
      (RingHom.ext fun _ => rfl) hx
  · intro hx
    exact IsIntegral.map_of_comp_eq (S := E) (U := E) e.toRingHom (RingHom.id E)
      (RingHom.ext fun _ => rfl) hx

omit [FiniteDimensional F E] in
theorem mem_integers_iff (x : E) : x ∈ integers F E ↔ x ∈ extensionIntegers F E := by
  rw [mem_integralClosure_iff, isIntegral_iff_baseIntegers, integral_iff_mem_spectralIntegers]

/-- The integral closure is the spectral integer ring of `E`. -/
def integersEquiv : integers F E ≃+* extensionIntegers F E :=
  RingEquiv.subringCongr (R := E) (s := (integers F E).toSubring)
    (t := (extensionIntegers F E).toSubring) (by
      ext x
      exact mem_integers_iff F E x)

omit [FiniteDimensional F E] in
@[simp] theorem coe_integersEquiv (x : integers F E) :
    ((integersEquiv F E x : extensionIntegers F E) : E) = x := rfl

instance : IsLocalRing (integers F E) := (integersEquiv F E).symm.isLocalRing

omit [FiniteDimensional F E] in
theorem mem_maximalIdeal_integersEquiv_iff (x : integers F E) :
    integersEquiv F E x ∈ maximalIdeal (extensionIntegers F E) ↔
      x ∈ maximalIdeal (integers F E) := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_map_iff (integersEquiv F E) x]

/-- A finite Galois intermediate field inside the inertia fixed field has trivial inertia. -/
theorem inertia_eq_bot [IsGalois F E] (hE : E ≤ inertiaFixedField F) : inertia F E = ⊥ := by
  have hres := (arithmeticUnramified_iff_residue_finrank F E).mp
    ((finiteUnramifiedMaximality F E).mp hE)
  have : IsGalois (ResidueField (baseIntegers F)) (ResidueField (extensionIntegers F E)) :=
    isGalois_of_finite_base _ _
  have : FiniteDimensional (ResidueField (baseIntegers F))
      (ResidueField (extensionIntegers F E)) :=
    Module.Finite.of_restrictScalars_finite (baseIntegers F) _ _
  have hcard : Nat.card (E ≃ₐ[F] E) ≤
      Nat.card Gal(ResidueField (extensionIntegers F E)/ResidueField (baseIntegers F)) := by
    rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, hres]
  have hinj := ((residueHom_surjective F E).bijective_of_nat_card_le hcard).1
  exact (MonoidHom.ker_eq_bot_iff _).mpr hinj

end Spectral

section Galois

variable [IsGalois F E]

/-- Galois automorphisms of `E/F` restricted to the ring of integers. -/
def galoisAction : (E ≃ₐ[F] E) →* (integers F E ≃ₐ[𝒪[F]] integers F E) :=
  (galRestrict 𝒪[F] F E (integers F E)).toMonoidHom

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] [IsGalois F E] in
@[simp] theorem coe_galoisAction_apply (σ : E ≃ₐ[F] E) (x : integers F E) :
    ((galoisAction F E σ x : integers F E) : E) = σ x :=
  algebraMap_galRestrict_apply 𝒪[F] σ x

theorem card_galois : Nat.card (E ≃ₐ[F] E) = Module.finrank 𝒪[F] (integers F E) := by
  rw [finrank_integers, IsGalois.card_aut_eq_finrank]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F
local instance : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

/-- For `E` inside the inertia fixed field, the Galois group acts faithfully on the residue field
of the ring of integers. -/
theorem galoisAction_faithful (hE : E ≤ inertiaFixedField F) (g : E ≃ₐ[F] E)
    (hg : ∀ x : integers F E,
      residue (integers F E) (galoisAction F E g x) = residue (integers F E) x) :
    g = 1 := by
  have hmem : g ∈ inertia F E := by
    change residueHom F E g = 1
    ext y
    obtain ⟨y, rfl⟩ := residue_surjective y
    change residue _ (integerAut F E g y) = residue _ y
    let x := (integersEquiv F E).symm y
    have hx : galoisAction F E g x - x ∈ maximalIdeal (integers F E) := by
      rw [← residue_eq_zero_iff, RingHom.map_sub, hg x, sub_self]
    have hxy : integersEquiv F E (galoisAction F E g x - x) = integerAut F E g y - y := by
      apply Subtype.ext
      change ((galoisAction F E g x : integers F E) : E) - (x : E) = g (y : E) - (y : E)
      rw [coe_galoisAction_apply]
      rfl
    have hy : integerAut F E g y - y ∈ maximalIdeal (extensionIntegers F E) := by
      rw [← hxy]
      exact (mem_maximalIdeal_integersEquiv_iff F E _).mpr hx
    rw [← sub_eq_zero, ← RingHom.map_sub, residue_eq_zero_iff]
    exact hy
  rw [inertia_eq_bot F E hE] at hmem
  exact Subgroup.mem_bot.mp hmem

end Galois

end LocalUnramified

open LocalUnramified in
/-- **Unramified integral cocycle vanishing over a local field (KP Lemma 8.1.4).** Let `M` be a
smooth integral model of `G` over `𝒪[F]` with connected special fibre, and let `E/F` be a finite
Galois extension inside the inertia fixed field. Every crossed homomorphism
`Gal(E/F) → G(E)` whose values have integral coordinates for `M` is the coboundary of a point
with integral coordinates. -/
def LocalUnramifiedIntegralCocycleVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (M : IntegralModel 𝒪[F] F G),
    M.IsSmooth →
    ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left →
    ∀ (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E],
      E ≤ LocalGalois.Separable.inertiaFixedField F →
      ∀ c : (E ≃ₐ[F] E) → G.affinePoints (CommAlgCat.of F E),
        (∀ σ τ, c (σ * τ) = c σ * GaloisPoint.conjugate F E G σ (c τ)) →
        (∀ σ, M.HasIntegralCoordinates E (c σ)) →
        ∃ f : G.affinePoints (CommAlgCat.of F E), M.HasIntegralCoordinates E f ∧
          ∀ σ, c σ = f * (GaloisPoint.conjugate F E G σ f)⁻¹

open LocalUnramified in
theorem localUnramifiedIntegralCocycleVanishing :
    LocalUnramifiedIntegralCocycleVanishingStatement.{u} := by
  intro F _ _ _ _ G M hM hconn E _ _ hE c hc hint
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : Finite (𝒪[F] ⧸ 𝓂[F]) := inferInstanceAs (Finite 𝓀[F])
  obtain ⟨f, hf, hcob⟩ := M.exists_integral_coboundary E (integers F E) (MonoidHom.id _)
    (galoisAction F E) 𝓂[F] hM hconn (coe_galoisAction_apply F E) (card_galois F E)
    (galoisAction_faithful F E hE) c hc
    (fun σ a => (mem_integralClosure_iff _ _).mpr (hint σ a))
  exact ⟨f, fun a => (mem_integralClosure_iff _ _).mp (hf a), hcob⟩

namespace GaloisCocycle

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Twisting the Galois values of a cocycle by a point `g` gives a crossed homomorphism. -/
theorem twistedValue_mul (ξ : Cocycle G (cover k L)) (g : G.affinePoints (CommAlgCat.of k L))
    (σ τ : L ≃ₐ[k] L) :
    g⁻¹ * value ξ (σ * τ) * GaloisPoint.conjugate k L G (σ * τ) g =
      (g⁻¹ * value ξ σ * GaloisPoint.conjugate k L G σ g) *
        GaloisPoint.conjugate k L G σ (g⁻¹ * value ξ τ * GaloisPoint.conjugate k L G τ g) := by
  rw [value_mul, GaloisPoint.conjugate_mul, map_mul, map_mul, map_inv]
  group

variable [FiniteDimensional k L] [IsGalois k L]

/-- If the twist of the Galois values of a cocycle by a point `g` is a Galois coboundary, the
cocycle is trivial. -/
theorem isTrivial_of_twist (ξ : Cocycle G (cover k L))
    (g f : G.affinePoints (CommAlgCat.of k L))
    (h : ∀ σ : L ≃ₐ[k] L, g⁻¹ * value ξ σ * GaloisPoint.conjugate k L G σ g =
      f * (GaloisPoint.conjugate k L G σ f)⁻¹) :
    ξ.IsTrivial := by
  refine (isTrivial_iff ξ).mpr ⟨g * f, fun σ => ?_⟩
  have hσ := h σ
  rw [map_mul, mul_inv_rev]
  calc value ξ σ = g * (g⁻¹ * value ξ σ * GaloisPoint.conjugate k L G σ g) *
        (GaloisPoint.conjugate k L G σ g)⁻¹ := by group
    _ = g * f * ((GaloisPoint.conjugate k L G σ f)⁻¹ *
        (GaloisPoint.conjugate k L G σ g)⁻¹) := by rw [hσ]; group

end GaloisCocycle

open LocalUnramified in
/-- **Cocycles that are integral after twisting.** Let `M` be a smooth integral model of `G` over
`𝒪[F]` with connected special fibre and `E/F` a finite Galois extension inside the inertia fixed
field. A cocycle of `G` on `Spec E → Spec F` whose Galois values, twisted by some point
`g ∈ G(E)`, have integral coordinates for `M` is trivial. -/
theorem GaloisCocycle.isTrivial_of_integral_twist
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} (M : IntegralModel 𝒪[F] F G) (hM : M.IsSmooth)
    (hconn : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left)
    {E : IntermediateField F (SeparableClosure F)} [FiniteDimensional F E] [IsGalois F E]
    (hE : E ≤ LocalGalois.Separable.inertiaFixedField F)
    (ξ : Cocycle G (GaloisCocycle.cover F E)) (g : G.affinePoints (CommAlgCat.of F E))
    (hg : ∀ σ : E ≃ₐ[F] E, M.HasIntegralCoordinates E
      (g⁻¹ * GaloisCocycle.value ξ σ * GaloisPoint.conjugate F E G σ g)) :
    ξ.IsTrivial := by
  obtain ⟨f, -, hf⟩ := localUnramifiedIntegralCocycleVanishing F G M hM hconn E hE
    (fun σ => g⁻¹ * GaloisCocycle.value ξ σ * GaloisPoint.conjugate F E G σ g)
    (GaloisCocycle.twistedValue_mul ξ g) hg
  exact GaloisCocycle.isTrivial_of_twist ξ g f hf

end Langlands.GroupScheme
