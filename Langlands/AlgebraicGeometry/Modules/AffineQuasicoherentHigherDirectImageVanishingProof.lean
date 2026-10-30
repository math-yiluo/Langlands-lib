import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingStatement
import Langlands.AlgebraicGeometry.Modules.AffineVanishing.QuasicoherentCech
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.Cohomology.CechFlasque

/-!
# Higher direct images of quasi-coherent modules along an affine morphism vanish: proof

Quasi-coherent modules have exact Čech complexes for standard open coverings of affine opens.
This property passes to the cokernel of an embedding into an injective module, and it makes
sections over affine opens exact. Since an affine morphism has affine preimages of affine
opens, a dimension shift shows that all higher direct images vanish (Stacks 01XC).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace AffineVanishing

open Langlands.Cohomology

section Sheaf

variable {T : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)}

lemma g_app_f_app (V : Opens T) (a : S.X₁.obj.obj (op V)) :
    S.g.hom.app (op V) (S.f.hom.app (op V) a) = 0 := by
  exact congrArg (fun φ : S.X₁ ⟶ S.X₃ => φ.hom.app (op V) a) S.zero

lemma injective_f_app (hS : S.ShortExact) (V : Opens T) :
    Function.Injective (S.f.hom.app (op V)) := by
  have := hS.mono_f
  have : Mono S.f.hom := (TopCat.Sheaf.forget AddCommGrpCat T).map_mono S.f
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

lemma exists_f_app_eq (hS : S.ShortExact) {V : Opens T} (b : S.X₂.obj.obj (op V))
    (hb : S.g.hom.app (op V) b = 0) : ∃ a, S.f.hom.app (op V) a = b :=
  TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f b hb

/-- A Čech `0`-cocycle consists of sections agreeing on overlaps. -/
lemma res_eq_res_of_d_zero_eq_zero {ι : Type*} {P : TopCat.Presheaf AddCommGrpCat.{u} T}
    {U : ι → Opens T} {u : Cech.C P U 0} (hu : Cech.d P U 0 u = 0) (i j : ι) {O : Opens T}
    (hi : O ≤ Cech.inter U (fun _ : Fin 1 => i)) (hj : O ≤ Cech.inter U (fun _ : Fin 1 => j)) :
    Cech.res hi (u fun _ => i) = Cech.res hj (u fun _ => j) := by
  let τ : Fin 2 → ι := Fin.cons i (fun _ : Fin 1 => j)
  have hO : O ≤ Cech.inter U τ :=
    (le_inf (hi.trans (Cech.inter_le_apply _ 0)) hj).trans (Cech.inter_cons U i _).ge
  have e₀ : τ ∘ (0 : Fin 2).succAbove = fun _ => j := Cech.cons_comp_succAbove_zero i _
  have e₁ : τ ∘ (1 : Fin 2).succAbove = fun _ => i := by
    funext a
    rw [Fin.fin_one_eq_zero a]
    rfl
  have h := congrArg (Cech.res hO) (congrFun hu τ)
  rw [Cech.d_apply, Fin.sum_univ_two, Pi.zero_apply, map_zero, map_add] at h
  simp only [map_neg, Cech.res_res, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul] at h
  have h' := add_neg_eq_zero.1 h
  calc Cech.res hi (u fun _ => i)
      = Cech.res (hO.trans (Cech.inter_le_comp τ (1 : Fin 2).succAbove))
          (u (τ ∘ (1 : Fin 2).succAbove)) := Cech.res_congr P U e₁.symm u _ _
    _ = Cech.res (hO.trans (Cech.inter_le_comp τ (0 : Fin 2).succAbove))
          (u (τ ∘ (0 : Fin 2).succAbove)) := h'.symm
    _ = Cech.res hj (u fun _ => j) := Cech.res_congr P U e₀ u _ _

end Sheaf

section Surjective

variable {X : Scheme.{u}}

/-- The Čech differential of the restrictions of one section over `W` vanishes in degree `0`. -/
lemma d_zero_res {ι : Type*} {W : X.Opens} (g : ι → Γ(X, W))
    (P : TopCat.Presheaf AddCommGrpCat.{u} X) (s : P.obj (op W)) :
    Cech.d P (cover g) 0 (fun σ => Cech.res (inter_le g σ) s) = 0 := by
  funext τ
  rw [Cech.d_apply, Fin.sum_univ_two]
  simp only [Cech.res_res, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Pi.zero_apply]
  exact add_neg_eq_zero.2 rfl

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}

/-- If `0 ⟶ F ⟶ G ⟶ H ⟶ 0` is a short exact sequence of abelian sheaves on `X` and `F` has
vanishing first Čech cohomology for all standard covers of an affine open `V`, then
`G(V) ⟶ H(V)` is surjective. -/
theorem surjective_app_of_exactAt (hS : S.ShortExact) {V : X.Opens} (hV : IsAffineOpen V)
    (hG : ∀ (ι : Type u) [Finite ι] (g : ι → Γ(X, V)), Ideal.span (Set.range g) = ⊤ →
      Cech.ExactAt S.X₁.obj (cover g) 0) :
    Function.Surjective (S.g.hom.app (op V)) := by
  classical
  intro s
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).2 hS.epi_g)
  let L : Set Γ(X, V) := {h | ∃ t : S.X₂.obj.obj (op (X.basicOpen h)),
    S.g.hom.app _ t = Cech.res (X.basicOpen_le h) s}
  have hL : Ideal.span L = ⊤ := by
    rw [← hV.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun h => X.basicOpen_le h.1) fun x hx => ?_
    obtain ⟨O, hOV, ⟨t, ht⟩, hxO⟩ := hloc V s x hx
    obtain ⟨h, hhO, hxh⟩ := hV.exists_basicOpen_le (V := O) ⟨x, hxO⟩ hx
    have ht' : S.g.hom.app (op O) t = Cech.res hOV s := ht
    refine Opens.mem_iSup.2 ⟨⟨h, ?_⟩, hxh⟩
    show ∃ t : S.X₂.obj.obj (op (X.basicOpen h)), S.g.hom.app _ t = Cech.res (X.basicOpen_le h) s
    refine ⟨Cech.res hhO t, ?_⟩
    rw [Cech.map_res, ht', Cech.res_res]
  obtain ⟨s', hs'L, hs'⟩ := (Ideal.span_eq_top_iff_finite L).1 hL
  let g : s' → Γ(X, V) := Subtype.val
  have hg : Ideal.span (Set.range g) = ⊤ := by
    have : Set.range g = (s' : Set Γ(X, V)) := by
      ext x
      simp [g]
    rw [this, hs']
  have hL' : ∀ i : s', ∃ t : S.X₂.obj.obj (op (X.basicOpen (g i))),
      S.g.hom.app _ t = Cech.res (X.basicOpen_le (g i)) s := fun i => hs'L i.2
  choose t ht using hL'
  let t' : Cech.C S.X₂.obj (cover g) 0 := fun σ =>
    Cech.res (Cech.inter_le_apply σ 0) (t (σ 0))
  have ht' : Cech.map (cover g) S.g.hom 0 t' = fun σ => Cech.res (inter_le g σ) s := by
    funext σ
    simp only [Cech.map, AddMonoidHom.coe_mk, ZeroHom.coe_mk, t', Cech.map_res, ht, Cech.res_res]
  have hdt' : ∀ τ, S.g.hom.app _ (Cech.d S.X₂.obj (cover g) 0 t' τ) = 0 := by
    intro τ
    have := congrFun (Cech.d_map (cover g) S.g.hom 0 t') τ
    rw [ht', d_zero_res] at this
    exact this.symm
  choose b hb using fun τ => exists_f_app_eq hS _ (hdt' τ)
  have hb' : Cech.map (cover g) S.f.hom 1 b = Cech.d S.X₂.obj (cover g) 0 t' := funext hb
  have hdb : Cech.d S.X₁.obj (cover g) 1 b = 0 := by
    funext τ
    apply injective_f_app hS
    have := congrFun (Cech.d_map (cover g) S.f.hom 1 b) τ
    rw [hb', Cech.d_d] at this
    rw [Pi.zero_apply, map_zero]
    exact this.symm
  obtain ⟨a, ha⟩ := hG s' g hg b hdb
  let u : Cech.C S.X₂.obj (cover g) 0 := t' - Cech.map (cover g) S.f.hom 0 a
  have hu : Cech.d S.X₂.obj (cover g) 0 u = 0 := by
    simp only [u, map_sub, Cech.d_map, ha, hb', sub_self]
  have hπu : ∀ σ, S.g.hom.app _ (u σ) = Cech.res (inter_le g σ) s := by
    intro σ
    have h₁ : S.g.hom.app _ (t' σ) = Cech.res (inter_le g σ) s := congrFun ht' σ
    have h₂ : u σ = t' σ - S.f.hom.app _ (a σ) := rfl
    rw [h₂, map_sub, h₁, g_app_f_app, sub_zero]
  let sf : ∀ i : s', S.X₂.obj.obj (op (cover g i)) := fun i =>
    Cech.res (le_iInf fun _ => le_rfl : cover g i ≤ Cech.inter (cover g) (fun _ : Fin 1 => i))
      (u fun _ => i)
  have hsf : TopCat.Presheaf.IsCompatible S.X₂.obj (cover g) sf := by
    intro i j
    change Cech.res _ (Cech.res _ _) = Cech.res _ (Cech.res _ _)
    exact (Cech.res_res _ _ _).trans
      ((res_eq_res_of_d_zero_eq_zero hu i j _ _).trans (Cech.res_res _ _ _).symm)
  have hcover : V ≤ iSup (cover g) := (hV.iSup_basicOpen_eq_self_iff.2 hs').ge
  obtain ⟨T', hT', -⟩ := S.X₂.existsUnique_gluing' (cover g) V
    (fun i => homOfLE (X.basicOpen_le (g i))) hcover sf hsf
  refine ⟨T', S.X₃.eq_of_locally_eq' (cover g) V (fun i => homOfLE (X.basicOpen_le (g i)))
    hcover _ _ fun i => ?_⟩
  change Cech.res _ (S.g.hom.app _ T') = Cech.res _ s
  have hT'i : Cech.res (X.basicOpen_le (g i)) T' = sf i := hT' i
  refine (Cech.map_res S.g.hom _ T').symm.trans ?_
  rw [hT'i]
  exact (Cech.map_res S.g.hom _ _).trans
    ((congrArg (Cech.res _) (hπu fun _ => i)).trans (Cech.res_res _ _ _))

end Surjective

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module whose ordered Čech complex is exact in positive degrees for every cover of an
affine open `W` by basic opens `D(g i)`, with the `g i` generating the unit ideal of `Γ(X, W)`. -/
def IsCechAcyclic (G : X.Modules) : Prop :=
  ∀ (W : X.Opens), IsAffineOpen W → ∀ (ι : Type u) [Finite ι] (g : ι → Γ(X, W)),
    Ideal.span (Set.range g) = ⊤ → ∀ p, Cech.ExactAt G.presheaf (cover g) p

lemma isCechAcyclic_of_isQuasicoherent (M : X.Modules) [M.IsQuasicoherent] : IsCechAcyclic M :=
  fun _ hW _ _ g hg p => exactAt_cover g M hW hg p

/-- In a short exact sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` of `𝒪_X`-modules with `I` injective,
if `G` is Čech-acyclic then so is `Q`. -/
lemma isCechAcyclic_X₃ {S : ShortComplex X.Modules} (hS : S.ShortExact) [Injective S.X₂]
    (hG : IsCechAcyclic S.X₁) : IsCechAcyclic S.X₃ := by
  intro W hW ι _ g hg p
  have hS' : (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).ShortExact := hS.map_of_exact _
  have : TopCat.Presheaf.IsFlasque (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).X₂.obj :=
    PushforwardInjectiveAcyclic.isFlasque_of_injective S.X₂
  have hB := Cech.exactAt_of_isFlasque (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).X₂
    (cover g) p
  exact Cech.exactAt_of_shortExact (cover g)
    (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).f.hom
    (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).g.hom
    (fun _ _ a => g_app_f_app _ a)
    (fun _ _ => injective_f_app hS' _)
    (fun _ _ b hb => exists_f_app_eq hS' b hb)
    (fun _ σ => surjective_app_of_exactAt hS' (isAffineOpen_inter g hW σ)
      (fun κ _ g' hg' => hG _ (isAffineOpen_inter g hW σ) κ g' hg' 0))
    hB (hG W hW ι g hg (p + 1))

/-- For an affine morphism `f` and a short exact sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` with `G`
Čech-acyclic, the pushforward `f_* I ⟶ f_* Q` is an epimorphism. -/
lemma epi_pushforward_map {Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (hG : IsCechAcyclic S.X₁) :
    Epi ((Scheme.Modules.pushforward f).map S.g) := by
  have hS' : (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).ShortExact := hS.map_of_exact _
  refine ClosedImmersionHigherDirectImageVanishing.epi_of_isLocallySurjective _ ?_
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro V t y hy
  obtain ⟨V', hV', hyV', hV'V⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) hy
  have hA : IsAffineOpen (f ⁻¹ᵁ V') := (show IsAffineOpen V' from hV').preimage f
  obtain ⟨s, hs⟩ := surjective_app_of_exactAt hS' hA (fun κ _ g' hg' => hG _ hA κ g' hg' 0)
    (Cech.res (P := S.X₃.presheaf) (fun _ hx => hV'V hx : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V) t)
  exact ⟨V', hV'V, ⟨s, hs⟩, hyV'⟩

/-- Higher direct images of Čech-acyclic modules along an affine morphism vanish. -/
theorem isZero_higherDirectImage_of_isCechAcyclic {Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (q : ℕ) (G : X.Modules) (hG : IsCechAcyclic G) :
    IsZero ((DerivedSections.higherDirectImage f (q + 1)).obj G) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard Y.Modules
  let F := Scheme.Modules.pushforward f
  change IsZero ((F.rightDerived (q + 1)).obj G)
  induction q generalizing G with
  | zero =>
    have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact G
    have := Langlands.Cohomology.DerivedPlus.epi_rightDerivedδ_of_isZero F hS 0 1 rfl
      (F.isZero_rightDerived_obj_injective_succ 0 (Injective.under G))
    refine IsZero.of_epi_eq_zero (Langlands.Cohomology.DerivedPlus.rightDerivedδ F hS 0 1 rfl) ?_
    have h0 : Epi ((F.rightDerived 0).map (PushforwardInjectiveAcyclic.injectiveSc G).g) := by
      have e : (F.rightDerived 0).map (PushforwardInjectiveAcyclic.injectiveSc G).g =
          (F.rightDerivedZeroIsoSelf.hom.app _ ≫
            F.map (PushforwardInjectiveAcyclic.injectiveSc G).g) ≫
            F.rightDerivedZeroIsoSelf.inv.app _ := by
        rw [← F.rightDerivedZeroIsoSelf.hom.naturality, Category.assoc,
          Iso.hom_inv_id_app, Category.comp_id]
      have := epi_pushforward_map f hS hG
      rw [e]
      infer_instance
    rw [← cancel_epi ((F.rightDerived 0).map (PushforwardInjectiveAcyclic.injectiveSc G).g),
      Langlands.Cohomology.DerivedPlus.rightDerived_map_comp_δ, comp_zero]
  | succ n ih =>
    have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact G
    have := Langlands.Cohomology.DerivedPlus.epi_rightDerivedδ_of_isZero F hS (n + 1) (n + 2) rfl
      (F.isZero_rightDerived_obj_injective_succ (n + 1) (Injective.under G))
    exact IsZero.of_epi (Langlands.Cohomology.DerivedPlus.rightDerivedδ F hS (n + 1) (n + 2) rfl)
      (ih (cokernel (Injective.ι G)) (isCechAcyclic_X₃ hS hG))

end AffineVanishing

open AffineVanishing in
/-- Higher direct images of quasi-coherent modules along an affine morphism vanish in every
positive degree. -/
theorem affineQuasicoherentHigherDirectImageVanishing :
    AffineQuasicoherentHigherDirectImageVanishingStatement.{u} := by
  intro X S f _ M _ q
  exact isZero_higherDirectImage_of_isCechAcyclic f q M (isCechAcyclic_of_isQuasicoherent M)

end Langlands.AlgebraicGeometry.Modules
