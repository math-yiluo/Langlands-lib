import Langlands.Representation.CuspidalSupport.HeckeAlgebraCenterFiniteStatement
import Langlands.Representation.CuspidalSupport.FiniteTypeCenterAdmissibleStatement

/-!
# Algebraic reduction of the Hecke-centre finiteness corollary

The categorical centre acts through the ring centre of a level Hecke algebra.
The coset permutation representation is cyclic, so finite-type centre
admissibility implies the unchanged Renard VI.10.7 Corollary.
The finite-type admissibility premise remains an independent proof obligation.
-/

noncomputable section

universe uR uG

open CategoryTheory

namespace Langlands.Shimura.LevelHecke

open Langlands.Induction

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : OpenSubgroup G)

private abbrev D : SmoothRep.{uR, uG, max uG uR} R G :=
  smoothPermutation R R K.toSubgroup K.isOpen

/-- The underlying finitely supported function of a level Hecke element. -/
def heckeEmbedding :
    LevelHeckeAlgebra R K.toSubgroup →ₗ[R] (G ⧸ K.toSubgroup →₀ R) :=
  (fixedVectors (permRep R K.toSubgroup) K.toSubgroup).subtype.comp
    (LevelHeckeAlgebra.ofHeckeSpace K.toSubgroup).symm.toLinearMap

omit [IsTopologicalGroup G] in
theorem heckeEmbedding_injective : Function.Injective (heckeEmbedding (R := R) K) :=
  Subtype.val_injective.comp (LevelHeckeAlgebra.ofHeckeSpace K.toSubgroup).symm.injective

/-- A natural central endomorphism acts on the level Hecke algebra by
multiplication by a central element. -/
theorem categoricalCenter_hecke
    (z : CatCenter (SmoothRep.{uR, uG, max uG uR} R G)) :
    ∃ c ∈ Subring.center (LevelHeckeAlgebra R K.toSubgroup),
      ∀ h : LevelHeckeAlgebra R K.toSubgroup,
        SmoothRep.hom (z.app (D K)) (heckeEmbedding K h) =
          heckeEmbedding K (c * h) := by
  let f := SmoothRep.hom (z.app (D K))
  let c : HeckeSpace R K.toSubgroup K.toSubgroup :=
    fixedVectorsMap f K.toSubgroup (unitElement K.toSubgroup)
  have hright (h : HeckeSpace R K.toSubgroup K.toSubgroup) :
      f (h : G ⧸ K.toSubgroup →₀ R) =
        (heckeMul R K.toSubgroup K.toSubgroup K.toSubgroup h c :
          G ⧸ K.toSubgroup →₀ R) := by
    have hn := fixedVectorsMap_heckeAct f K.toSubgroup K.toSubgroup h
      (unitElement K.toSubgroup)
    change fixedVectorsMap f K.toSubgroup
      (heckeAct (permRep R K.toSubgroup) K.toSubgroup K.toSubgroup h
        (unitElement K.toSubgroup)) = _ at hn
    rw [heckeAct_permRep_unitElement] at hn
    exact congrArg Subtype.val hn
  have hleft (h : HeckeSpace R K.toSubgroup K.toSubgroup) :
      f (h : G ⧸ K.toSubgroup →₀ R) =
        (heckeMul R K.toSubgroup K.toSubgroup K.toSubgroup c h :
          G ⧸ K.toSubgroup →₀ R) := by
    let q : D K ⟶ D K := SmoothRep.ofHom (frobenius (permRep R K.toSubgroup) h)
    have hn := congrArg
      (fun a : D K ⟶ D K =>
        SmoothRep.hom a (unitElement (R := R) K.toSubgroup : G ⧸ K.toSubgroup →₀ R))
      (z.naturality q)
    change f (frobenius (permRep R K.toSubgroup) h
      (unitElement (R := R) K.toSubgroup : G ⧸ K.toSubgroup →₀ R)) =
        frobenius (permRep R K.toSubgroup) h
          (f (unitElement (R := R) K.toSubgroup : G ⧸ K.toSubgroup →₀ R)) at hn
    rw [frobenius_unitElement] at hn
    exact hn
  let e := LevelHeckeAlgebra.ofHeckeSpace (R := R) K.toSubgroup
  refine ⟨e c, ?_, fun h => hleft (e.symm h)⟩
  rw [Subring.mem_center_iff]
  intro h
  apply heckeEmbedding_injective K
  exact (hright (e.symm h)).symm.trans (hleft (e.symm h))

/-- Finite generation under the categorical centre implies finite generation
over the ring centre of the level Hecke algebra. -/
theorem finite_center_of_categorical_generators
    (hgen : ∃ (n : ℕ) (s : Fin n → LevelHeckeAlgebra R K.toSubgroup),
      ∀ h : LevelHeckeAlgebra R K.toSubgroup,
        ∃ z : Fin n → CatCenter (SmoothRep.{uR, uG, max uG uR} R G),
          heckeEmbedding K h =
            ∑ i, SmoothRep.hom ((z i).app (D K)) (heckeEmbedding K (s i))) :
    Module.Finite (Subring.center (LevelHeckeAlgebra R K.toSubgroup))
      (LevelHeckeAlgebra R K.toSubgroup) := by
  classical
  obtain ⟨n, s, hs⟩ := hgen
  apply Module.Finite.of_fg_top
  apply Submodule.fg_iff_exists_fin_generating_family.mpr
  refine ⟨n, s, top_unique ?_⟩
  intro h _
  obtain ⟨z, hz⟩ := hs h
  choose c hc hact using fun i => categoricalCenter_hecke K (z i)
  have heq : h = ∑ i, (⟨c i, hc i⟩ :
      Subring.center (LevelHeckeAlgebra R K.toSubgroup)) • s i := by
    apply heckeEmbedding_injective K
    rw [map_sum, hz]
    exact Finset.sum_congr rfl fun i _ => hact i (s i)
  rw [heq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The permutation representation on cosets is cyclic over the group algebra. -/
theorem permRep_finite (L : Subgroup G) :
    Module.Finite (MonoidAlgebra R G) (permRep R L).asModule := by
  classical
  let ρ := permRep R L
  let e := ρ.asModuleEquiv
  let v := e.symm (Finsupp.single ((1 : G) : G ⧸ L) (1 : R))
  let S := Submodule.span (MonoidAlgebra R G) ({v} : Set ρ.asModule)
  have hsingle (q : G ⧸ L) (r : R) : e.symm (Finsupp.single q r) ∈ S := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have heq : e.symm (Finsupp.single (g : G ⧸ L) r) =
        MonoidAlgebra.single g r • v := by
      apply e.injective
      change Finsupp.single (g : G ⧸ L) r =
        ρ.asAlgebraHom (MonoidAlgebra.single g r) (e v)
      rw [Representation.asAlgebraHom_single]
      change Finsupp.single (g : G ⧸ L) r =
        r • permutation R G (G ⧸ L) R g (Finsupp.single ((1 : G) : G ⧸ L) 1)
      rw [permutation_single, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        Finsupp.smul_single_one]
    rw [heq]
    exact S.smul_mem _ (Submodule.subset_span (Set.mem_singleton v))
  have hall (a : G ⧸ L →₀ R) : e.symm a ∈ S := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using S.add_mem ha hb
    | single q r => exact hsingle q r
  apply Module.Finite.of_fg_top
  refine ⟨{v}, ?_⟩
  apply top_unique
  intro x _
  simpa only [S, Finset.coe_singleton, LinearEquiv.symm_apply_apply] using hall (e x)

end Langlands.Shimura.LevelHecke

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Shimura.LevelHecke

/-- The finite-type centre-admissibility theorem implies the full
Hecke-algebra corollary at its unchanged universes and hypotheses. -/
def HeckeAlgebraCenterFiniteReductionStatement.{u} : Prop :=
  FiniteTypeCenterAdmissibleStatement.{u, u} →
    HeckeAlgebraCenterFiniteStatement.{u}

theorem heckeAlgebraCenterFinite_of_finiteTypeCenterAdmissible :
    HeckeAlgebraCenterFiniteReductionStatement.{uG} := by
  intro hadm k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ K hK
  let D := Induction.smoothPermutation ℂ ℂ K.toSubgroup K.isOpen
  let H := LevelHeckeAlgebra ℂ K.toSubgroup
  have hfinite : Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      D.representation.asModule := permRep_finite K.toSubgroup
  obtain ⟨n, s, hs, hspan⟩ := hadm k G hG D hfinite K hK
  let e := LevelHeckeAlgebra.ofHeckeSpace (R := ℂ) K.toSubgroup
  let t : Fin n → H := fun i => e ⟨s i, fun g => hs i g g.property⟩
  have hgen : ∃ (n : ℕ) (t : Fin n → H), ∀ h : H,
      ∃ z : Fin n → CatCenter (SmoothRep.{0, uG, uG} ℂ (rationalPoints G)),
        heckeEmbedding K h =
          ∑ i, SmoothRep.hom ((z i).app D) (heckeEmbedding K (t i)) := by
    refine ⟨n, t, fun h => ?_⟩
    exact hspan (heckeEmbedding K h) (fun g hg => (e.symm h).property ⟨g, hg⟩)
  exact ⟨hgen, categoricalCenter_hecke K, finite_center_of_categorical_generators K hgen⟩

end Langlands.Aubert.General.RepresentedParabolic
