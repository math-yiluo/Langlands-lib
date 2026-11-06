import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement

/-! # Degenerate Jacquet modules and vanishing pieces of the geometric lemma

If the Levi `M` of a represented parabolic `P = MU` is all of `P`, the radical has trivial
rational points, so the normalized Jacquet module of a smooth representation `π` along `P`
is `π` itself restricted to `M(F)`: the coinvariants by the trivial subgroup are the whole
space and the modulus character is trivial. Separately, a graded piece of the geometric
lemma vanishes as soon as its Jacquet module does.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.HaarModulus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The Haar modulus of conjugation on the trivial subgroup is one. -/
theorem normalizerCharacter_eq_one_of_eq_bot (U : Subgroup G) [LocallyCompactSpace U]
    (hU : U = ⊥) (g : Subgroup.normalizer (U : Set G)) : normalizerCharacter U g = 1 := by
  have : Finite U := by subst hU; infer_instance
  refine normalizerCharacter_eq_one_of_preimage U ⊤ ?_ g ?_
  · rw [OpenSubgroup.coe_top]
    exact isCompact_univ
  · rw [OpenSubgroup.coe_top, Set.preimage_univ]

variable [LocallyCompactSpace G]

/-- The inverse half modulus of a normalizing subgroup acting on the trivial subgroup is
trivial. -/
theorem closedInverseHalfCharacter_eq_one_of_eq_bot (U : Subgroup G)
    (hU : IsClosed (U : Set G)) (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hbot : U = ⊥) (m : M) : closedInverseHalfCharacter U hU M hMU m = 1 := by
  let := hU.locallyCompactSpace
  rw [closedInverseHalfCharacter, Jacquet.inverseHalfCharacter_eq_one]
  exact normalizerCharacter_eq_one_of_eq_bot U hbot _

end Langlands.HaarModulus

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] {G P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- If the Levi `l : M ⟶ P` is an isomorphism, the radical `r : U ⟶ P` has trivial image on
rational points in `G(F)`: a point `r(u) = l(m)` has two factorizations `l(m) r(1) = l(1) r(u)`,
so `u = 1`. -/
theorem pointImage_radical_eq_bot_of_isIso_levi (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hmul : IsIso (subgroupMultiplication l r)) [IsIso l] :
    pointImage (r ≫ p) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  rw [Subgroup.mem_bot]
  have hlm : rationalPoints.map l (rationalPoints.map (inv l) (rationalPoints.map r u)) =
      rationalPoints.map r u := by
    rw [← pointMap_comp_apply, IsIso.inv_hom_id]
    simp [rationalPoints.map_apply]
  have h : rationalPoints.map l (rationalPoints.map (inv l) (rationalPoints.map r u)) *
      rationalPoints.map r 1 = rationalPoints.map l 1 * rationalPoints.map r u := by
    rw [hlm, map_one, map_one, mul_one, one_mul]
  have hu : u = 1 := ((eq_and_eq_of_pointMultiplication l r hmul h).2).symm
  rw [hu, map_one]

variable [TopologicalSpace k] [IsAffineHom G.X.hom]

local instance degenerateAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The relations defining the coinvariants by the radical vanish when the Levi is all of
the parabolic. -/
theorem jacquetRelations_eq_bot_of_isIso_levi (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hmul : IsIso (subgroupMultiplication l r)) [IsIso l]
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    Jacquet.Localization.relations π.representation (pointImage (r ≫ p)) 1 = ⊥ := by
  have hbot := pointImage_radical_eq_bot_of_isIso_levi p l r hmul
  rw [Jacquet.Localization.relations, Submodule.span_eq_bot]
  rintro _ ⟨⟨w, x⟩, rfl⟩
  have hw : w = 1 := by
    apply Subtype.ext
    have hw : (w : rationalPoints G) ∈ (⊥ : Subgroup (rationalPoints G)) := hbot ▸ w.2
    exact Subgroup.mem_bot.mp hw
  subst hw
  simp

/-- If the Levi `l : M ⟶ P` is all of `P`, the normalized Jacquet module of `π` along `P`,
read on `M(F)`, is the space of `π` itself: the coinvariants by the trivial radical. -/
def fullLeviJacquetEquiv (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) [IsIso l]
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    (leviJacquetFunctor p l r hp hr hl hmul).obj π ≃ₗ[ℂ] π :=
  Submodule.quotEquivOfEqBot _ (jacquetRelations_eq_bot_of_isIso_levi p l r hmul π)

/-- The equivalence sends the coinvariant class of `x` to `x`. -/
theorem fullLeviJacquetEquiv_mk (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) [IsIso l]
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (x : π) :
    fullLeviJacquetEquiv p l r hp hr hl hmul π
      (Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x) = x :=
  rfl

/-- The equivalence intertwines the Jacquet action of `m ∈ M(F)` with the action of its image
`(l ≫ p)(m) ∈ G(F)` on `π`. -/
theorem fullLeviJacquetEquiv_representation (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) [IsIso l]
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (m : rationalPoints M) (x : (letI := leviPointTopology l hl
      (leviJacquetFunctor p l r hp hr hl hmul).obj π)) :
    letI := leviPointTopology l hl
    fullLeviJacquetEquiv p l r hp hr hl hmul π
        (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation m x) =
      π.representation (rationalPoints.map (l ≫ p) m)
        (fullLeviJacquetEquiv p l r hp hr hl hmul π x) := by
  let := leviPointTopology l hl
  obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective π.representation (pointImage (r ≫ p)) 1 x
  rw [leviJacquetFunctor_obj_representation]
  erw [normalizedJacquetFunctor_obj_apply]
  rw [HaarModulus.closedInverseHalfCharacter_eq_one_of_eq_bot _ _ _ _
    (pointImage_radical_eq_bot_of_isIso_levi p l r hmul)]
  simp only [Units.val_one, one_smul]
  erw [fullLeviJacquetEquiv_mk p l r hp hr hl hmul π,
    fullLeviJacquetEquiv_mk p l r hp hr hl hmul π]

namespace GeometricLemmaIntersectionDatum

variable {N Q L V : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : V ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- A graded piece `i^L_{Q'} ∘ ι ∘ r^M_{P'}` of the geometric lemma vanishes on `ρ` as soon
as the Jacquet module `r^M_{P'} ρ` does: its functions take values in that Jacquet module. -/
theorem subsingleton_pieceFunctor_obj
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hρ : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      Subsingleton ((jacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ)) :
    Subsingleton (D.pieceFunctor.obj ρ) :=
  ⟨fun _ _ => Subtype.ext (Subtype.ext (funext fun _ => @Subsingleton.elim _ hρ _ _))⟩

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
