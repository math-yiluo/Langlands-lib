import Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement

/-! The rank-zero boundary of the cuspidal embedding theorem. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uG

private def emptyShape : BlockShape 0 where
  length := 0
  size := Fin.elim0
  positive i := Fin.elim0 i
  sum_eq := by simp

private def trivialGroupSubmoduleOrderIso
    {G : Type uG} [Group G] [Subsingleton G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    Subrepresentation ρ ≃o Submodule ℂ V where
  toFun := Subrepresentation.toSubmodule
  invFun S := ⟨S, by
    intro g v hv
    rw [Subsingleton.elim g 1, map_one]
    exact hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private theorem trivialGroupSmooth
    {G : Type uG} [Group G] [Subsingleton G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : IsSmooth ρ := by
  intro v
  refine ⟨⊤, ?_⟩
  intro g
  change ρ (g : G) v = v
  rw [Subsingleton.elim (g : G) 1, map_one]
  rfl

private def trivialGroupInductionMap
    {G : Type uG} [Group G] [Subsingleton G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (P : Subgroup G)
    (σ : Representation ℂ P V) :
    ρ.IntertwiningMap (Induction.smoothInduced P σ) where
  toLinearMap :=
    { toFun v := Induction.smoothFunctionOf P σ (fun _ => v)
        (by
          intro p x
          rw [Subsingleton.elim p 1, map_one]
          rfl)
        ⊤ (fun _ _ => rfl)
      map_add' _ _ := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      map_smul' _ _ := by
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  isIntertwining' g := by
    simp only [Subsingleton.elim g 1, map_one]
    rfl

private theorem trivialGroupInductionMap_injective
    {G : Type uG} [Group G] [Subsingleton G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (P : Subgroup G)
    (σ : Representation ℂ P V) :
    Function.Injective (trivialGroupInductionMap ρ P σ) := by
  intro v w h
  exact congrArg (fun f => Induction.eval P σ f 1) h

/-- The published zero-rank target, with independent field and carrier universes. -/
theorem zeroRankCuspidalEmbedding
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) :
    ZeroRankCuspidalEmbeddingTheorem.{uF, uV} F T := by
  let := T.topology
  let := T.generalLinearTopologicalGroup 0
  intro ω hω
  let : ω.IsIrreducible := hω
  let : IsSimpleModule ℂ ω :=
    (isSimpleModule_iff ℂ ω).mpr
      ((trivialGroupSubmoduleOrderIso ω.representation).isSimpleOrder_iff.mp hω)
  let : Module.Finite ℂ ω := inferInstance
  have hωa : ω.IsAdmissible := ⟨ω.isSmooth, fun _ => inferInstance⟩
  let B := emptyShape
  let : Subsingleton (B.Levi F.Carrier) :=
    ⟨by intro f g; funext i; exact Fin.elim0 i⟩
  let σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
    SmoothRep.of (Representation.trivial ℂ (B.Levi F.Carrier) ω)
      (trivialGroupSmooth _)
  have hσ : σ.IsIrreducible :=
    (trivialGroupSubmoduleOrderIso σ.representation).isSimpleOrder_iff.mpr
      ((isSimpleModule_iff ℂ ω).mp inferInstance)
  have hσa : IsAdmissible σ.representation :=
    ⟨σ.isSmooth, fun _ => inferInstance⟩
  have hσq : IsLeviQuasicuspidal B σ.representation := by
    intro S hS
    apply False.elim
    apply hS
    apply top_unique
    intro g _
    rw [Subsingleton.elim g 1]
    exact (Geometric.refinedParabolic F.Carrier B S).one_mem
  refine ⟨hωa, B, σ, hσ, ⟨hσa, hσq⟩, ?_⟩
  exact ⟨trivialGroupInductionMap ω.representation _ _,
    trivialGroupInductionMap_injective ω.representation _ _⟩

end Langlands.CuspidalSupport
