import Langlands.Representation.CuspidalSupport.StandardLeviFixedVectorSupportStatements
import Langlands.Representation.CuspidalSupport.StandardRepresentativeFixedVectorHelpers
import Langlands.Representation.Jacquet.RationalInducedFixedVectors
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Renard VI.10.6, Corollary, first claim: the representative fixed-vector criterion

For a standard cuspidal datum `a = (M_I, σ)` and a compact open `K` with the level hypotheses of
`StandardRepresentativeFixedVectorCriterionStatement`, some irreducible representation with
inertial support `[M_I, σ]_G` has a nonzero `K`-fixed vector iff `σ^{K ∩ M_I} ≠ 0`.

* `exists_leviPoint_conj_mem_of_normalLevel`: for any `g ∈ G`, the Iwasawa factorization
  `g = p k` (`p ∈ P_J`, `k ∈ K₀`) gives `m ∈ M_J` (the Levi part of `p`) with
  `m⁻¹ (g x g⁻¹) m ∈ K` whenever `x ∈ K` and `g x g⁻¹ ∈ M_J`.
* `nontrivial_literalLeviFixedVectors_rationalIsoPullback`: along an actual Levi conjugacy
  `c : M_I → M_J`, nonzero `K ∩ M_J`-fixed vectors of `B` give nonzero `K ∩ M_I`-fixed vectors of
  the transported representation `c.iso^* B`.
* `nontrivial_literalLeviFixedVectors_of_inertialSupport`: direction (⇒).
* `representativeFixedVectorCriterion`: the iff for one standard family.
* `standardRepresentativeFixedVectorCriterion`: the target statement. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.CuspidalSupport

open GroupScheme Aubert.General Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open BruhatTits.SpecialCompact
open Langlands.Jacquet

/-- The group-theoretic core of the transport, for an abstract semidirect decomposition
`P = M ⋉ U` of a group `H`. Let `K₀` normalize `K`, and let the Levi projection `P → M` map
`K ∩ P` into `K`. For `p ∈ P`, `k ∈ K₀` and `m` the Levi part of `p`: if `x ∈ K` and
`y = (p k) x (p k)⁻¹ ∈ M`, then `m⁻¹ y m ∈ K`. Indeed, with `u = m⁻¹ p ∈ U` and
`z = m⁻¹ y m ∈ M`, the element `k x k⁻¹ = u⁻¹ z u` lies in `K ∩ P` and has Levi part `z`. -/
theorem levi_conj_mem_of_projection_mem {H : Type*} [Group H] {P M U K K₀ : Subgroup H}
    (D : IsSemidirectDecomposition P M U)
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set H))
    (hproj : ∀ q : P, (q : H) ∈ K → ((D.projection q : M) : H) ∈ K)
    (p : P) (k : K₀) {x : H} (hxK : x ∈ K)
    (hy : (p : H) * k * x * ((p : H) * k)⁻¹ ∈ M) :
    ((D.projection p : M) : H)⁻¹ * ((p : H) * k * x * ((p : H) * k)⁻¹) *
      ((D.projection p : M) : H) ∈ K := by
  have hu : ((D.projection p : M) : H)⁻¹ * (p : H) ∈ U := D.projection_inv_mul_mem p
  set m : H := ((D.projection p : M) : H) with hm_def
  have hmL : m ∈ M := (D.projection p).2
  set u : H := m⁻¹ * (p : H) with hu_def
  set z : H := m⁻¹ * ((p : H) * k * x * ((p : H) * k)⁻¹) * m with hz_def
  have hz : z ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hmL) hy) hmL
  have hk : (k : H) * x * (k : H)⁻¹ = u⁻¹ * z * u := by
    rw [hu_def, hz_def]
    group
  have hkK : (k : H) * x * (k : H)⁻¹ ∈ K := (hnormal k.2 x).mp hxK
  have huP : u ∈ P := D.unipotent_le hu
  have hzP : z ∈ P := D.levi_le hz
  let q : P := ⟨u⁻¹ * z * u, P.mul_mem (P.mul_mem (P.inv_mem huP) hzP) huP⟩
  have hq : D.projection q = ⟨z, hz⟩ := by
    rw [D.projection_eq_iff]
    have hzN : z⁻¹ ∈ Subgroup.normalizer (U : Set H) :=
      (Subgroup.normalizer _).inv_mem (D.levi_le_normalizer hz)
    have h1 : z⁻¹ * u⁻¹ * z⁻¹⁻¹ ∈ U := (hzN u⁻¹).mp (U.inv_mem hu)
    have h2 : z⁻¹ * (u⁻¹ * z * u) = (z⁻¹ * u⁻¹ * z⁻¹⁻¹) * u := by group
    change z⁻¹ * (u⁻¹ * z * u) ∈ U
    rw [h2]
    exact U.mul_mem h1 hu
  have hqK : (q : H) ∈ K := by
    change u⁻¹ * z * u ∈ K
    rw [← hk]
    exact hkK
  have := hproj q hqK
  rw [hq] at this
  exact this

/-- The algebraic core of the fixed-vector transport. Let `L_I, L_J, K` be subgroups of a group
`Γ`, let `t : H_J → L_J` have the multiplicative left inverse `s : L_J → H_J`, and let
`φ : L_I → H_J` satisfy `t (φ x) = g x g⁻¹` in `Γ`. Assume `m ∈ L_J` satisfies
`m⁻¹ (g x g⁻¹) m ∈ K` whenever `x ∈ K` and `g x g⁻¹ ∈ L_J`. If `v` is fixed by `ρ (s z)` for
every `z ∈ K ∩ L_J`, then `ρ (s m) v` is fixed by `ρ (φ x)` for every `x ∈ K ∩ L_I`. -/
theorem representation_conj_fixed_of_levi_conj_mem {Γ HJ V : Type*} [Group Γ] [Group HJ]
    [AddCommGroup V] [Module ℂ V] {LI LJ K : Subgroup Γ} {FS : Type*} [FunLike FS LJ HJ]
    [MonoidHomClass FS LJ HJ] (t : HJ → LJ) (s : FS) (hst : ∀ y, s (t y) = y)
    (φ : LI → HJ) (g : Γ) (hφ : ∀ x : LI, ((t (φ x) : LJ) : Γ) = g * (x : Γ) * g⁻¹)
    (m : LJ) (hm : ∀ x : Γ, x ∈ K → g * x * g⁻¹ ∈ LJ → (m : Γ)⁻¹ * (g * x * g⁻¹) * m ∈ K)
    (ρ : Representation ℂ HJ V) (v : V)
    (hv : ∀ z ∈ K.comap LJ.subtype, ρ (s z) v = v) :
    ∀ x ∈ K.comap LI.subtype, ρ (φ x) (ρ (s m) v) = ρ (s m) v := by
  intro x hxK
  rw [Subgroup.mem_comap, Subgroup.coe_subtype] at hxK
  have hyL : g * (x : Γ) * g⁻¹ ∈ LJ := hφ x ▸ (t (φ x)).2
  have hzK : m⁻¹ * t (φ x) * m ∈ K.comap LJ.subtype := by
    rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hφ x]
    exact hm x hxK hyL
  have hvz := hv _ hzK
  simp only [map_mul, map_inv, hst, Module.End.mul_apply] at hvz
  have h := congrArg (ρ (s m)) hvz
  rwa [Representation.self_inv_apply] at h

/-- A nonzero vector stays nonzero under the action of a group element. -/
theorem representation_apply_ne_zero {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (h : H) {w : V} (hw : w ≠ 0) : ρ h w ≠ 0 := fun h0 =>
  hw (by rw [← Representation.inv_self_apply ρ h w, h0, map_zero])

/-- A nonzero fixed vector of a pulled-back smooth representation, read in the original
representation: if the `L`-fixed space of `e^* A` is nontrivial, then some nonzero `v ∈ A` is
fixed by `A(e x)` for every `x ∈ L`. -/
theorem exists_ne_zero_of_nontrivial_fixedVectors_pullback {H₁ H₂ : Type*} [Group H₁]
    [TopologicalSpace H₁] [Group H₂] [TopologicalSpace H₂] (e : H₁ ≃ₜ* H₂)
    (A : SmoothRep.{0, _, uV} ℂ H₂) (L : Subgroup H₁)
    (h : Nontrivial (fixedVectors (SmoothRep.pullback e A).representation L)) :
    ∃ v : A, v ≠ 0 ∧ ∀ x ∈ L, A.representation (e x) v = v := by
  obtain ⟨v, hv⟩ := exists_ne (0 : fixedVectors (SmoothRep.pullback e A).representation L)
  exact ⟨v.val, fun h0 => hv (Subtype.ext h0), fun x hx => v.property ⟨x, hx⟩⟩

/-- A nonzero vector of `A` fixed by `A(e₂ (e₁ x))` for every `x ∈ L` makes the `L`-fixed space
of the twice pulled-back representation `e₁^* e₂^* A` nontrivial. -/
theorem nontrivial_fixedVectors_pullback_pullback {H₁ H₂ H₃ : Type*} [Group H₁]
    [TopologicalSpace H₁] [Group H₂] [TopologicalSpace H₂] [Group H₃] [TopologicalSpace H₃]
    (e₁ : H₁ ≃ₜ* H₂) (e₂ : H₂ ≃ₜ* H₃) (A : SmoothRep.{0, _, uV} ℂ H₃) (L : Subgroup H₁)
    (w : A) (hw0 : w ≠ 0) (hw : ∀ x ∈ L, A.representation (e₂ (e₁ x)) w = w) :
    Nontrivial (fixedVectors
      (SmoothRep.pullback e₁ (SmoothRep.pullback e₂ A)).representation L) :=
  ⟨⟨⟨w, fun x => hw x.1 x.2⟩, 0, fun h0 => hw0 (congrArg Subtype.val h0)⟩⟩

section Local

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance representativeCriterionProofAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance representativeCriterionProofAmbientTopology :
    TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance representativeCriterionProofLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance representativeCriterionProofLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance representativeCriterionProofLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance representativeCriterionProofLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

attribute [local irreducible] Standard.leviScheme

omit [LocallyOfFiniteType G.X.hom] in
/-- On rational points, an actual Levi conjugacy `c` between the standard Levis `M_I` and `M_J`
is conjugation by its point: `c(x) = g x g⁻¹` inside `G(F)`, for `g = c.point`. -/
theorem leviRationalPointHomeomorph_rationalPointIso_coe
    (I J : Finset (SimpleRoot i ν))
    (c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν I))
      (Standard.leviHom i ν (rootSet i ν J)))
    (x : rationalPoints (bernsteinLeviScheme i ν I)) :
    (leviRationalPointHomeomorph i ν J (rationalPointIso c.iso x) : rationalPoints G) =
      c.point * (leviRationalPointHomeomorph i ν I x : rationalPoints G) * c.point⁻¹ := by
  rw [leviRationalPointHomeomorph_apply_coe, leviRationalPointHomeomorph_apply_coe,
    rationalPointIso_apply]
  have h : rationalPoints.map
      (Standard.leviHom i ν (rootSet i ν I) ≫ (G.innerIso c.point).hom) x =
      rationalPoints.map (c.iso.hom ≫ Standard.leviHom i ν (rootSet i ν J)) x := by
    rw [c.commutes]
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, ← Category.assoc] at h
  rw [rationalPoints.map_apply, rationalPoints.map_apply, ← h]
  have hc := congrArg (fun f => f (rationalPoints.map (Standard.leviHom i ν (rootSet i ν I)) x))
    (congrArg DFunLike.coe (rationalPoints_map_innerIso c.point))
  simp only [rationalPoints.map_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply] at hc
  exact hc

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

include family in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The Levi modification of a conjugating point. Write `g = p k` with `p ∈ P_J` and `k ∈ K₀`
(`standard_parabolic_factorization_of_minimal`), and let `m ∈ M_J` be the Levi part of `p`. If
`x ∈ K` and `g x g⁻¹ ∈ M_J`, then `m⁻¹ (g x g⁻¹) m ∈ K`
(`levi_conj_mem_of_projection_mem`, with the projection property
`standard_projection_mem_of_iwahoriIntersection` of the Iwahori decomposition of `K`). -/
theorem exists_leviPoint_conj_mem_of_normalLevel
    (J : Finset (SimpleRoot i ν)) (K : Subgroup (rationalPoints G))
    (K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
    (hIwahori : HasIwahoriIntersectionDecomposition K (levi i ν J)
      (unipotent i ν J) (standardOppositeUnipotentPoints i ν (rootSet i ν J)))
    (g : rationalPoints G) :
    ∃ m : levi i ν J, ∀ x : rationalPoints G, x ∈ K → g * x * g⁻¹ ∈ levi i ν J →
      (m : rationalPoints G)⁻¹ * (g * x * g⁻¹) * m ∈ K := by
  obtain ⟨p, k, hg⟩ := standard_parabolic_factorization_of_minimal i ν family J K₀ hIwasawa g
  refine ⟨(family.decomposition J).projection p, fun x hxK hy => ?_⟩
  subst hg
  exact levi_conj_mem_of_projection_mem (family.decomposition J) hnormal
    (standard_projection_mem_of_iwahoriIntersection i ν family J K hIwahori) p k hxK hy

include family in
omit [LocallyOfFiniteType G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- Transport of literal Levi fixed vectors along an actual Levi conjugacy `c : M_I → M_J`: if
`B` has a nonzero `K ∩ M_J`-fixed vector, then `c.iso^* B` has a nonzero `K ∩ M_I`-fixed vector.
With `m` from `exists_leviPoint_conj_mem_of_normalLevel` for `g = c.point`, the translate
`B(m) v` of a `K ∩ M_J`-fixed vector `v` is the required vector
(`representation_conj_fixed_of_levi_conj_mem`). -/
theorem nontrivial_literalLeviFixedVectors_rationalIsoPullback
    (I J : Finset (SimpleRoot i ν))
    (c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν I))
      (Standard.leviHom i ν (rootSet i ν J)))
    (K : Subgroup (rationalPoints G)) (K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
    (hIwahori : HasIwahoriIntersectionDecomposition K (levi i ν J)
      (unipotent i ν J) (standardOppositeUnipotentPoints i ν (rootSet i ν J)))
    (B : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J)))
    (hB : Nontrivial (fixedVectors (bernsteinLiteralLeviRep i ν J B).representation
      (K.comap (levi i ν J).subtype))) :
    Nontrivial (fixedVectors
      (bernsteinLiteralLeviRep i ν I (rationalIsoPullback c.iso B)).representation
      (K.comap (levi i ν I).subtype)) := by
  obtain ⟨m, hm⟩ := exists_leviPoint_conj_mem_of_normalLevel i ν family J K K₀ hnormal
    hIwasawa hIwahori c.point
  obtain ⟨v, hv0, hvJ⟩ := exists_ne_zero_of_nontrivial_fixedVectors_pullback
    (leviRationalPointHomeomorph i ν J).symm B (K.comap (levi i ν J).subtype) hB
  have hφ : ∀ x : levi i ν I,
      ((leviRationalPointHomeomorph i ν J
        (rationalPointIso c.iso ((leviRationalPointHomeomorph i ν I).symm x)) : levi i ν J) :
          rationalPoints G) = c.point * (x : rationalPoints G) * c.point⁻¹ := fun x => by
    rw [leviRationalPointHomeomorph_rationalPointIso_coe, ContinuousMulEquiv.apply_symm_apply]
  have key := representation_conj_fixed_of_levi_conj_mem
    (leviRationalPointHomeomorph i ν J) (leviRationalPointHomeomorph i ν J).symm
    (leviRationalPointHomeomorph i ν J).symm_apply_apply
    (fun x => rationalPointIso c.iso ((leviRationalPointHomeomorph i ν I).symm x))
    c.point hφ m hm B.representation v hvJ
  exact nontrivial_fixedVectors_pullback_pullback (leviRationalPointHomeomorph i ν I).symm
    (rationalPointIso c.iso) B (K.comap (levi i ν I).subtype) _
    (representation_apply_ne_zero B.representation _ hv0) key

/-- Direction (⇒) of the representative criterion: if `π` has inertial support `[a]` and a
nonzero `K`-fixed vector, then `σ^{K ∩ M_I} ≠ 0`. With `π` a subquotient of `i(b)` for a datum
`b` inertially related to `a` through a conjugacy `c`, Mackey gives `b^{K ∩ M_J} ≠ 0`, the
transport gives `(c.iso^* b)^{K ∩ M_I} ≠ 0`, and Mackey once more together with the invariance of
induced fixed vectors under unramified twists returns to `a`. -/
theorem nontrivial_literalLeviFixedVectors_of_inertialSupport
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
    (hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
    (hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
      HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
        (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hπ : IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π)
    (hπK : Nontrivial (fixedVectors π.representation K.toSubgroup)) :
    Nontrivial (fixedVectors
      (bernsteinLiteralLeviRep i ν a.roots a.representation).representation
      (K.toSubgroup.comap (levi i ν a.roots).subtype)) := by
  obtain ⟨b, hb, hπb⟩ := hπ
  obtain ⟨c, hrel⟩ := (bernsteinInertialClass_eq_iff i ν family a b).mp hb.symm
  have hbK : Nontrivial (fixedVectors
      (bernsteinLiteralLeviRep i ν b.roots b.representation).representation
      (K.toSubgroup.comap (levi i ν b.roots).subtype)) :=
    (exists_bernsteinCuspidalSupport_fixedVectors_iff i ν family b K hK K₀ hnormal hIwasawa
      (hIwahori _ (rootSet_subset i ν b.roots))).mp ⟨π, hπb, hπK⟩
  have hdK := nontrivial_literalLeviFixedVectors_rationalIsoPullback i ν family a.roots b.roots c
    K.toSubgroup K₀ hnormal hIwasawa (hIwahori _ (rootSet_subset i ν b.roots))
    b.representation hbK
  have hdInd : Nontrivial (fixedVectors (rationalStandardInduction i ν family a.roots
      (rationalIsoPullback c.iso b.representation)).representation K.toSubgroup) :=
    (nontrivial_standardInduction_fixedVectors_iff i ν family a.roots K hK K₀ hnormal hIwasawa
      (hIwahori _ (rootSet_subset i ν a.roots)) _).mpr hdK
  have haInd : Nontrivial (fixedVectors (rationalStandardInduction i ν family a.roots
      a.representation).representation K.toSubgroup) :=
    (nontrivial_inductionFixedVectors_iff_of_rationalInertiaRelated i ν family a.roots K hK
      hrel).mpr hdInd
  exact (nontrivial_standardInduction_fixedVectors_iff i ν family a.roots K hK K₀ hnormal
    hIwasawa (hIwahori _ (rootSet_subset i ν a.roots)) _).mp haInd

/-- The representative criterion for one standard family: some irreducible representation with
inertial support `[a]` has a nonzero `K`-fixed vector iff `σ^{K ∩ M_I} ≠ 0`. -/
theorem representativeFixedVectorCriterion
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
    (hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
    (hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
      HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
        (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)) :
    ∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      (∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
          IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π ∧
            Nontrivial (fixedVectors π.representation K.toSubgroup)) ↔
        Nontrivial (fixedVectors
          (bernsteinLiteralLeviRep i ν a.roots a.representation).representation
          (K.toSubgroup.comap (levi i ν a.roots).subtype)) := by
  intro a
  constructor
  · rintro ⟨π, hπ, hπK⟩
    exact nontrivial_literalLeviFixedVectors_of_inertialSupport i ν family K hK K₀ hnormal
      hIwasawa hIwahori a π hπ hπK
  · exact exists_bernsteinInertialSupport_fixedVectors_of_literalLevi i ν family a K hK K₀
      hnormal hIwasawa (hIwahori _ (rootSet_subset i ν a.roots))

end Local

/-- Renard VI.10.6, Corollary, first claim (`StandardRepresentativeFixedVectorCriterionStatement`):
for a standard cuspidal datum `a = (M_I, σ)` and a compact open `K` normalized by a compact `K₀`
with the minimal Iwasawa decomposition, and with the Iwahori decomposition of `K` along every
standard parabolic, `[M_I, σ]_G ∈ B(G)_K` iff `σ^{K ∩ M_I} ≠ 0`. -/
theorem standardRepresentativeFixedVectorCriterion :
    StandardRepresentativeFixedVectorCriterionStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro S i hi ν hν _hstandard K₀ _hK₀ hIwasawa K hK _hKK₀ hnormal hIwahori
  let : T2Space F := BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  exact representativeFixedVectorCriterion i ν (standardBernsteinFamily i ν hG hi hν)
    K hK K₀ hnormal hIwasawa hIwahori

end Langlands.CuspidalSupport
