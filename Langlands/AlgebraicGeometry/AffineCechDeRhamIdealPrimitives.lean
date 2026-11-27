import Langlands.AlgebraicGeometry.AffineCechDeRhamInfinitesimalMorphism
import Langlands.Cohomology.CechRefine

/-! # Normalizing degree-zero Čech primitives on a square-zero reduction -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (U : Scheme.AffineOpenCover.{u} X)

/-- In degree zero the Čech differential is the second restriction minus the first. -/
lemma cechD_zero_eq_sub_restrict (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (a : Cochains U P 0) (τ : Fin 2 → U.I₀) :
    cechD U P 0 a τ = restrictCochain P a τ (fun _ => 1) -
      restrictCochain P a τ (fun _ => 0) := by
  have h₀ : (0 : Fin 2).succAbove = (fun _ => 1) := funext fun i => by fin_cases i; rfl
  have h₁ : (1 : Fin 2).succAbove = (fun _ => 0) := funext fun i => by fin_cases i; rfl
  rw [cechD_apply, Fin.sum_univ_two]
  change (1 : ℤ) • restrictCochain P a τ (0 : Fin 2).succAbove +
    (-1 : ℤ) • restrictCochain P a τ (1 : Fin 2).succAbove = _
  rw [h₀, h₁, one_smul, neg_one_smul, sub_eq_add_neg]

private lemma reduction_restrict {Z : Scheme.{u}} (r : Z ⟶ X)
    {W W' : X.Opens} (e : W' ≤ W) :
    X.presheaf.map (homOfLE e).op ≫ r.appLE W' (r ⁻¹ᵁ W') le_rfl =
      r.appLE W (r ⁻¹ᵁ W) le_rfl ≫ Z.presheaf.map (homOfLE (r.preimage_mono e)).op := by
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

private lemma reduce_constant (I : Ideal R) (W : X.Opens) (a : R) :
    let r := quotientReductionMap f I
    let p := pullback.snd f (quotientBaseMap I)
    (r.appLE W (r ⁻¹ᵁ W) le_rfl).hom
      (algebraMap R ((sectionAlgebras f).obj (op W)) a) =
      (p.appLE ⊤ (r ⁻¹ᵁ W) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv.hom (Ideal.Quotient.mk I a)) := by
  let r := quotientReductionMap f I
  let p := pullback.snd f (quotientBaseMap I)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫
    r.appLE W (r ⁻¹ᵁ W) le_rfl).hom a =
    (p.appLE ⊤ (r ⁻¹ᵁ W) le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv.hom (Ideal.Quotient.mk I a))
  rw [Scheme.Hom.appLE_comp_appLE, show r ≫ f = p ≫ quotientBaseMap I from pullback.condition,
    ← Scheme.Hom.appLE_comp_appLE p (quotientBaseMap I) ⊤ ⊤ (r ⁻¹ᵁ W) le_top le_top,
    ← Category.assoc,
    show (quotientBaseMap I).appLE ⊤ ⊤ le_top = (quotientBaseMap I).appTop from
      (quotientBaseMap I).app_eq_appLE.symm, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- A degree-zero function primitive for an ideal-valued coboundary can be
normalized to take values in the extended base ideal when the actual reduced
scheme has only constant global functions. -/
theorem exists_ideal_primitive_of_cechD_mem [IsSeparated f] (I : Ideal R)
    (hconst : Function.Surjective (pullback.snd f (quotientBaseMap I)).appTop.hom)
    (a : C0 f U)
    (ha : ∀ τ : Fin 2 → U.I₀,
      cechD U (functions f) 0 a τ ∈ I.map (algebraMap R (tupleSections f U τ))) :
    ∃ b : C0 f U, cechD U (functions f) 0 b = cechD U (functions f) 0 a ∧
      ∀ σ : Fin 1 → U.I₀, b σ ∈ I.map (algebraMap R (tupleSections f U σ)) := by
  let Z := quotientReduction f I
  let r := quotientReductionMap f I
  let p := pullback.snd f (quotientBaseMap I)
  let W (σ : Fin 1 → U.I₀) := inter (coverOpens U) σ
  let W₀ (σ : Fin 1 → U.I₀) : Z.Opens := r ⁻¹ᵁ W σ
  let a₀ (σ : Fin 1 → U.I₀) : Γ(Z, W₀ σ) := (r.appLE (W σ) (W₀ σ) le_rfl).hom (a σ)
  have hW₀ : ⊤ ≤ iSup W₀ := by
    intro z _
    have hz : r z ∈ ⨆ i, coverOpens U i := by
      rw [show (⨆ i, coverOpens U i) = ⊤ from U.openCover.iSup_opensRange]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
    apply Opens.mem_iSup.mpr
    refine ⟨fun _ => i, ?_⟩
    change r z ∈ Langlands.Cohomology.Cech.inter (coverOpens U) (fun _ : Fin 1 => i)
    rw [Langlands.Cohomology.Cech.inter_const_one]
    exact hi
  have hcomp : TopCat.Presheaf.IsCompatible Z.sheaf.1 W₀ a₀ := by
    intro σ σ'
    have constant (v : Fin 1 → U.I₀) : ∃ i, v = fun _ => i :=
      ⟨v 0, funext fun k => by fin_cases k; rfl⟩
    obtain ⟨i, rfl⟩ := constant σ
    obtain ⟨j, rfl⟩ := constant σ'
    let τ : Fin 2 → U.I₀ := ![i, j]
    let T := inter (coverOpens U) τ
    let T₀ := r ⁻¹ᵁ T
    have hn : T = W (fun _ => i) ⊓ W (fun _ => j) := by
      change Langlands.Cohomology.Cech.inter (coverOpens U) ![i, j] =
        Langlands.Cohomology.Cech.inter (coverOpens U) (fun _ : Fin 1 => i) ⊓
          Langlands.Cohomology.Cech.inter (coverOpens U) (fun _ : Fin 1 => j)
      rw [Langlands.Cohomology.Cech.inter_two, Langlands.Cohomology.Cech.inter_const_one,
        Langlands.Cohomology.Cech.inter_const_one]
    have hzero : (r.appLE T T₀ le_rfl).hom (cechD U (functions f) 0 a τ) = 0 := by
      rw [← RingHom.mem_ker, (quotientReductionMap_appLE f I T (isAffineOpen_inter f U τ)).2]
      exact ha τ
    rw [cechD_zero_eq_sub_restrict, map_sub, sub_eq_zero] at hzero
    let e₀ : T ≤ W (fun _ => i) := inter_le_comp τ (fun _ : Fin 1 => 0)
    let e₁ : T ≤ W (fun _ => j) := inter_le_comp τ (fun _ : Fin 1 => 1)
    change ((X.presheaf.map (homOfLE e₁).op) ≫ r.appLE T T₀ le_rfl).hom (a (fun _ => j)) =
      ((X.presheaf.map (homOfLE e₀).op) ≫ r.appLE T T₀ le_rfl).hom (a (fun _ => i)) at hzero
    rw [reduction_restrict, reduction_restrict] at hzero
    have hzero' :
        (Z.presheaf.map (homOfLE (r.preimage_mono e₀)).op).hom (a₀ (fun _ => i)) =
        (Z.presheaf.map (homOfLE (r.preimage_mono e₁)).op).hom (a₀ (fun _ => j)) := hzero.symm
    have hin : W₀ (fun _ => i) ⊓ W₀ (fun _ => j) ≤ T₀ := by
      change r ⁻¹ᵁ W (fun _ => i) ⊓ r ⁻¹ᵁ W (fun _ => j) ≤ r ⁻¹ᵁ T
      rw [hn, Scheme.Hom.preimage_inf]
    have restrict (σ : Fin 1 → U.I₀) (e : T₀ ≤ W₀ σ) :
        (Z.presheaf.map (homOfLE hin).op).hom
            ((Z.presheaf.map (homOfLE e).op).hom (a₀ σ)) =
          (Z.presheaf.map (homOfLE (hin.trans e)).op).hom (a₀ σ) := by
      change ((Z.presheaf.map (homOfLE e).op) ≫ (Z.presheaf.map (homOfLE hin).op)).hom _ = _
      rw [← Functor.map_comp]
      rfl
    have he := congrArg ((Z.presheaf.map (homOfLE hin).op).hom) hzero'
    change (Z.presheaf.map (homOfLE hin).op).hom
        ((Z.presheaf.map (homOfLE (r.preimage_mono e₀)).op).hom (a₀ (fun _ => i))) =
      (Z.presheaf.map (homOfLE hin).op).hom
        ((Z.presheaf.map (homOfLE (r.preimage_mono e₁)).op).hom (a₀ (fun _ => j))) at he
    rw [restrict, restrict] at he
    exact he
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' W₀ ⊤ (fun _ => homOfLE le_top) hW₀ a₀ hcomp
  obtain ⟨c₀, hc₀⟩ := hconst s
  let c := (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).hom.hom c₀
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective c
  let base : C0 f U := fun σ => algebraMap R (tupleSections f U σ) d
  have hbase : cechD U (functions f) 0 base = 0 := by
    funext τ
    rw [cechD_zero_eq_sub_restrict]
    change restrictSections f U τ (fun _ : Fin 1 => 1) (algebraMap R _ d) -
      restrictSections f U τ (fun _ : Fin 1 => 0) (algebraMap R _ d) = 0
    rw [(restrictSections f U τ _).commutes, (restrictSections f U τ _).commutes, sub_self]
  refine ⟨a - base, by rw [map_sub, hbase, sub_zero], fun σ => ?_⟩
  change ((a σ : tupleSections f U σ) - (base σ : tupleSections f U σ)) ∈
    I.map (algebraMap R (tupleSections f U σ))
  rw [← (quotientReductionMap_appLE f I (W σ) (isAffineOpen_inter f U σ)).2]
  change (r.appLE (W σ) (W₀ σ) le_rfl).hom
    ((a σ : tupleSections f U σ) - (base σ : tupleSections f U σ)) = 0
  rw [map_sub, sub_eq_zero]
  change a₀ σ = (r.appLE (W σ) (W₀ σ) le_rfl).hom (algebraMap R (tupleSections f U σ) d)
  rw [reduce_constant, hd]
  have hcc : (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv.hom c = c₀ :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))) c₀
  rw [hcc, ← hs σ, ← hc₀]
  change (p.appTop ≫ Z.presheaf.map (homOfLE le_top).op).hom c₀ = _
  rw [show p.appTop = p.appLE ⊤ ⊤ le_top from p.app_eq_appLE, Scheme.Hom.appLE_map]

end Langlands.AlgebraicGeometry.AffineCechDeRham
