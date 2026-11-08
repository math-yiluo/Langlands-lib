import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupLocallyConstantSmoothSections
import Langlands.Sheaf.Equivariant.LocalAction

/-!
# Local actions on the finite rational transport site

Every object of the open-subgroup rational transport category carries the
action of its own open subgroup through the inverse-label operators. Taking as
admissible the local actions in which each element acts through the arrow
labelled by its inverse gives a local action system. Its discrete presheaves
are those on which every object's own subgroup acts with open stabilizers, and
for module sheaves this is the published local smoothness. For separated
presheaves on the finite covering topology, discreteness is equivalent to local
discreteness: finitely many restrictions fixed by open subgroups give one open
subgroup fixing the section.
-/

noncomputable section

universe u v r w uA wA

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Opposite Langlands.Sheaf.Equivariant

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

/-- The action of an object's own open subgroup through the inverse-label
operators. -/
def operatorAction (X : ρ.OpenSubgroupTransport) :
    (X.subgroup : Subgroup G) →* (End X)ᵐᵒᵖ where
  toFun k := MulOpposite.op (X.operator k)
  map_one' := congrArg MulOpposite.op X.operator_one
  map_mul' k l := congrArg MulOpposite.op (X.operator_mul k l)

@[simp]
theorem operatorAction_unop (X : ρ.OpenSubgroupTransport) (k : (X.subgroup : Subgroup G)) :
    (X.operatorAction k).unop = X.operator k := rfl

variable (ρ) in
/-- The admissible local actions on the transport site: every element of the
acting open subgroup acts through an arrow labelled by its inverse. -/
def localActionSystem : LocalActionSystem (ρ.OpenSubgroupTransport) G where
  IsAdmissible _ _ a := ∀ h, (a h).unop.label = (h : G)⁻¹

theorem isAdmissible_operatorAction (X : ρ.OpenSubgroupTransport) :
    (localActionSystem ρ).IsAdmissible X X.subgroup X.operatorAction :=
  fun _ => rfl

/-- On the elements common to the acting subgroup and the object's own
subgroup, an admissible local action is the operator action. -/
theorem IsAdmissible.eq_operatorAction {X : ρ.OpenSubgroupTransport} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End X)ᵐᵒᵖ} (ha : (localActionSystem ρ).IsAdmissible X H a)
    (g : G) (hgH : g ∈ H) (hgX : g ∈ X.subgroup) :
    a ⟨g, hgH⟩ = X.operatorAction ⟨g, hgX⟩ :=
  MulOpposite.unop_injective (Hom.ext (ha ⟨g, hgH⟩))

variable {A : Type uA} [Category A] {FA : A → A → Type*} {CA : A → Type wA}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{wA} A FA]

/-- A section is discrete for an admissible local action exactly when it is
discrete for the operator action of the object's own subgroup. -/
theorem isDiscreteSection_iff_operatorAction (F : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A)
    {X : ρ.OpenSubgroupTransport} {H : OpenSubgroup G} {a : (H : Subgroup G) →* (End X)ᵐᵒᵖ}
    (ha : (localActionSystem ρ).IsAdmissible X H a) (s : ToType (F.obj (op X))) :
    IsDiscreteSection F a s ↔ IsDiscreteSection F X.operatorAction s :=
  ⟨IsDiscreteSection.of_agree (N := H ⊓ X.subgroup) inf_le_left inf_le_right
      fun g _ => IsAdmissible.eq_operatorAction ha g _ _,
    IsDiscreteSection.of_agree (N := H ⊓ X.subgroup) inf_le_right inf_le_left
      fun g _ => (IsAdmissible.eq_operatorAction ha g _ _).symm⟩

/-- Discreteness only has to be checked for the operator action of each
object's own subgroup. -/
theorem isDiscrete_iff (F : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A) :
    (localActionSystem ρ).IsDiscrete F ↔
      ∀ (X : ρ.OpenSubgroupTransport) (s : ToType (F.obj (op X))),
        IsDiscreteSection F X.operatorAction s :=
  ⟨fun hF X s => hF X X.subgroup X.operatorAction (isAdmissible_operatorAction X) s,
    fun hF X _ _ ha s => (isDiscreteSection_iff_operatorAction F ha s).2 (hF X s)⟩

/-- Every arrow factors through an object with an admissible local action. -/
theorem admissibleSieve_eq_top (X : ρ.OpenSubgroupTransport) :
    (localActionSystem ρ).admissibleSieve X = ⊤ :=
  eq_top_iff.2 fun W g _ =>
    ⟨W, 𝟙 W, g, W.subgroup, W.operatorAction, isAdmissible_operatorAction W,
      Category.id_comp g⟩

theorem covers (J : GrothendieckTopology (ρ.OpenSubgroupTransport)) :
    (localActionSystem ρ).Covers J := fun X => by
  rw [admissibleSieve_eq_top]
  exact J.top_mem X

/-- Restriction along an arrow into an object `X` turns the action of an element
of `X`'s subgroup into the action of its conjugate on the source. -/
theorem comp_operator_eq {V X : ρ.OpenSubgroupTransport} (f : V ⟶ X)
    (g : (X.subgroup : Subgroup G)) (hg : f.label⁻¹ * (g : G) * f.label ∈ V.subgroup) :
    f ≫ X.operator g = V.operator ⟨_, hg⟩ ≫ f := by
  apply Hom.ext
  simp only [comp_label, operator_label]
  group

/-- For a presheaf separated for the finite covering topology, locally discrete
sections are discrete. -/
theorem isDiscrete_of_isLocallyDiscrete {F : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A}
    (hsep : Presheaf.IsSeparated (finiteTopology ρ) F)
    (hF : (localActionSystem ρ).IsLocallyDiscrete (finiteTopology ρ) F) :
    (localActionSystem ρ).IsDiscrete F := by
  rw [isDiscrete_iff]
  intro X s
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hF X s
  choose V k v H a ha hdisc hkv using hf
  have hop : ∀ i, IsDiscreteSection F (V i).operatorAction (F.map (v i).op s) :=
    fun i => (isDiscreteSection_iff_operatorAction F (ha i) _).1 (hdisc i)
  choose N hNle hNfix using hop
  have hcont : ∀ i, Continuous ((MulAut.conj (v i).label⁻¹).toMonoidHom : G → G) :=
    fun i => by
      change Continuous fun g : G => (v i).label⁻¹ * g * (v i).label⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
  let N' : I → OpenSubgroup G := fun i => (N i).comap _ (hcont i)
  have hN' : ∀ i (g : G), g ∈ N' i → (v i).label⁻¹ * g * (v i).label ∈ N i := by
    intro i g hg
    have hg' : (v i).label⁻¹ * g * (v i).label⁻¹⁻¹ ∈ N i := hg
    rwa [inv_inv] at hg'
  have : Fintype I := Fintype.ofFinite I
  refine ⟨X.subgroup ⊓ Finset.univ.inf N', inf_le_left, fun g hg => ?_⟩
  have hgN : ∀ i, (v i).label⁻¹ * (g : G) * (v i).label ∈ N i := fun i =>
    hN' i _ (SetLike.le_def.1 (Finset.inf_le (f := N') (Finset.mem_univ i))
      (OpenSubgroup.mem_inf.1 hg).2)
  have hcov : Sieve.ofArrows V v ∈ finiteTopology ρ X := by
    rw [ofArrows_mem_finiteTopology_iff]
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := hcover x hx
    refine ⟨i, ρ.toMonoidHom (k i).label • y, (k i).mapsTo y hy, ?_⟩
    rw [← hkv i, comp_label, map_mul, mul_smul]
  refine hsep X _ hcov _ _ fun W e he => ?_
  obtain ⟨i, e', rfl⟩ := (Sieve.mem_ofArrows_iff V v e).1 he
  rw [op_comp, F.map_comp, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  congr 1
  rw [operatorAction_unop, ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp,
    comp_operator_eq (v i) g (hNle i (hgN i)), op_comp, F.map_comp, CategoryTheory.comp_apply]
  exact hNfix i ⟨_, hNle i (hgN i)⟩ (hgN i)

/-- For a presheaf separated for the finite covering topology, discreteness and
local discreteness agree. -/
theorem isLocallyDiscrete_iff_isDiscrete {F : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A}
    (hsep : Presheaf.IsSeparated (finiteTopology ρ) F) :
    (localActionSystem ρ).IsLocallyDiscrete (finiteTopology ρ) F ↔
      (localActionSystem ρ).IsDiscrete F :=
  ⟨isDiscrete_of_isLocallyDiscrete hsep,
    LocalActionSystem.IsDiscrete.isLocallyDiscrete (localActionSystem ρ) (covers _)⟩

section Module

variable {R : Type r} [CommRing R]

/-- Module sheaves on the finite covering topology are separated. -/
theorem moduleSheaf_isSeparated (F : ModuleSheaf.{u, v, r, w} (ρ := ρ) R) :
    Presheaf.IsSeparated (finiteTopology ρ) F.obj := by
  intro X S hS x y h
  let E : Submodule R (F.obj.obj (op X)) := Submodule.span R {x - y}
  have hE : ModuleCat.ofHom E.subtype = (0 : ModuleCat.of R E ⟶ F.obj.obj (op X)) := by
    refine ((F.property (ModuleCat.of R E) S hS).isSeparatedFor).ext fun W f hf => ?_
    change ModuleCat.ofHom E.subtype ≫ F.obj.map f.op = 0 ≫ F.obj.map f.op
    rw [Limits.zero_comp]
    ext ⟨e, he⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 he
    change (F.obj.map f.op).hom (c • (x - y)) = 0
    rw [map_smul, map_sub]
    change c • ((F.obj.map f.op) x - (F.obj.map f.op) y) = 0
    rw [h W f hf, sub_self, smul_zero]
  have hxy := congrArg (fun φ => φ.hom ⟨x - y, Submodule.mem_span_singleton_self _⟩) hE
  exact sub_eq_zero.1 hxy

/-- For module sheaves, discreteness is the published smoothness of the section
representations at every object. -/
theorem isDiscrete_iff_locallySmoothProperty (F : ModuleSheaf.{u, v, r, w} (ρ := ρ) R) :
    (localActionSystem ρ).IsDiscrete F.obj ↔ locallySmoothProperty F := by
  rw [isDiscrete_iff]
  exact forall_congr' fun X => forall_congr' fun s =>
    isDiscreteSection_iff_isSmoothVector F.obj X.operatorAction s

/-- For module sheaves, local discreteness is the published smoothness of the
section representations at every object. -/
theorem isLocallyDiscrete_iff_locallySmoothProperty (F : ModuleSheaf.{u, v, r, w} (ρ := ρ) R) :
    (localActionSystem ρ).IsLocallyDiscrete (finiteTopology ρ) F.obj ↔
      locallySmoothProperty F :=
  (isLocallyDiscrete_iff_isDiscrete (moduleSheaf_isSeparated F)).trans
    (isDiscrete_iff_locallySmoothProperty F)

/-- The generic discrete sheaf property is the published local smoothness. -/
theorem discreteSheafProperty_eq :
    (localActionSystem ρ).discreteSheafProperty (ModuleCat.{w} R) (finiteTopology ρ) =
      locallySmoothProperty.{u, v, r, w} (ρ := ρ) (R := R) :=
  funext fun F => propext (isDiscrete_iff_locallySmoothProperty F)

/-- The generic smooth sheaf property is the published local smoothness. -/
theorem smoothSheafProperty_eq :
    (localActionSystem ρ).smoothSheafProperty (ModuleCat.{w} R) (finiteTopology ρ) =
      locallySmoothProperty.{u, v, r, w} (ρ := ρ) (R := R) :=
  funext fun F => propext (isLocallyDiscrete_iff_locallySmoothProperty F)

end Module

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
