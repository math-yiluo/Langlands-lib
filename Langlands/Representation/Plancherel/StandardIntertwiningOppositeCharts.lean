import Langlands.Representation.Plancherel.StandardIntertwiningDynamicSource
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct

/-! # Ordered charts for an opposite source radical and a common-Levi middle radical -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.StandardIntertwining

section Generic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- An actual intersection read inside its second factor is homeomorphic to
any subgroup with the same elements, by the identity on ambient elements. -/
def subgroupOfHomeomorphOfMem (A B C : Subgroup Γ)
    (h : ∀ g, g ∈ C ↔ g ∈ A ∧ g ∈ B) : A.subgroupOf B ≃ₜ C where
  toFun x := ⟨x.val.val, (h _).2 ⟨Subgroup.mem_subgroupOf.mp x.property, x.val.property⟩⟩
  invFun y := ⟨⟨y.val, ((h _).1 y.property).2⟩,
    Subgroup.mem_subgroupOf.mpr ((h _).1 y.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem subgroupOfHomeomorphOfMem_apply (A B C : Subgroup Γ)
    (h : ∀ g, g ∈ C ↔ g ∈ A ∧ g ∈ B) (x : A.subgroupOf B) :
    (subgroupOfHomeomorphOfMem A B C h x : Γ) = x.val.val := rfl

@[simp] theorem subgroupOfHomeomorphOfMem_symm_apply (A B C : Subgroup Γ)
    (h : ∀ g, g ∈ C ↔ g ∈ A ∧ g ∈ B) (y : C) :
    (((subgroupOfHomeomorphOfMem A B C h).symm y).val : Γ) = y.val := rfl

/-- A factor with only one point can be dropped from a product. -/
def trivialProdHomeomorph {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
    (t₀ : T) (ht : ∀ t, t = t₀) : T × X ≃ₜ X where
  toFun p := p.2
  invFun x := (t₀, x)
  left_inv p := Prod.ext (ht p.1).symm rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

/-- `Q ∩ C` is the ordered product of `Q ∩ A` and `Q ∩ B`: every element of `C`
lying in `Q` is `a * b` with `a ∈ A ∩ Q` and `b ∈ B ∩ Q`. -/
def HasCompactOpenProduct (Q : Set Γ) (A B C : Subgroup Γ) : Prop :=
  ∀ g ∈ C, g ∈ Q → ∃ a ∈ A, a ∈ Q ∧ ∃ b ∈ B, b ∈ Q ∧ g = a * b

end Generic

namespace OppositeCharts

open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]

local instance standardIntertwiningOppositeChartsIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance standardIntertwiningOppositeChartsTopologicalSpace : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

variable (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The radicals of a cocharacter and of its inverse meet trivially. -/
theorem eq_one_of_mem_inverse_radical {x : RationalPoint F G.X}
    (hx : x ∈ unipotentPoints (Dynamic.inverseCocharacter χ))
    (hx' : x ∈ unipotentPoints χ) : x = 1 :=
  Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hx
    (Dynamic.unipotent_le_parabolic χ _ hx')

variable {χ ψ}
variable (hZ : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) =
  (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)))

/-- The fixed contracting unit used to build the charts. The charts are literal
multiplication, so this choice does not affect them as maps. -/
def contractingUnit : Fˣ := (exists_unit_tendsto_pow_zero (F := F)).choose

/-- The powers of the fixed contracting unit converge to zero. -/
theorem contractingUnit_tendsto :
    Tendsto (fun n : ℕ => ((contractingUnit (F := F) : Fˣ) : F) ^ n) atTop (𝓝 0) :=
  (exists_unit_tendsto_pow_zero (F := F)).choose_spec

include hZ in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] in
/-- Every value of `ψ` lies in the common Levi points of `χ`. -/
theorem cocharPoint_mem_centralizer_left (t : Fˣ) :
    MatrixRepresentation.gmRationalPoint t ≫ ψ.hom.hom ∈
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
  rw [hZ, ← MatrixRepresentation.cocharPoint_eq_gmRationalPoint_comp]
  exact cocharPoint_mem_centralizer ψ t

include hZ in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] in
/-- Every value of `χ` lies in the common Levi points of `ψ`. -/
theorem cocharPoint_mem_centralizer_right (t : Fˣ) :
    MatrixRepresentation.gmRationalPoint t ≫ χ.hom.hom ∈
      (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)) := by
  rw [← hZ, ← MatrixRepresentation.cocharPoint_eq_gmRationalPoint_comp]
  exact cocharPoint_mem_centralizer χ t

include hZ in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- A common Levi point in the radical of the second cocharacter is trivial. -/
theorem eq_one_of_mem_centralizer_left_of_mem_radical
    {m : RationalPoint F G.X} (hm : m ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hmU : m ∈ unipotentPoints ψ) : m = 1 := by
  rw [hZ] at hm
  have h : m ∈ RationalPoint.levi ψ ⊓ RationalPoint.unipotent ψ := ⟨hm, hmU⟩
  rw [RationalPoint.levi_inf_unipotent] at h
  exact Subgroup.mem_bot.mp h

include hZ in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- A common Levi point in the radical of the first cocharacter is trivial. -/
theorem eq_one_of_mem_centralizer_right_of_mem_radical
    {m : RationalPoint F G.X} (hm : m ∈ (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)))
    (hmU : m ∈ unipotentPoints χ) : m = 1 := by
  rw [← hZ] at hm
  have h : m ∈ RationalPoint.levi χ ⊓ RationalPoint.unipotent χ := ⟨hm, hmU⟩
  rw [RationalPoint.levi_inf_unipotent] at h
  exact Subgroup.mem_bot.mp h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- The inverse of the inverse cocharacter, in the literal form used by the
published product theorem. -/
theorem inverse_inverseCocharacter :
    CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫
      Dynamic.inverseCocharacter χ = χ :=
  Dynamic.inverseCocharacter_inverseCocharacter χ

include hZ in
/-- The middle radical splits as its part in the inverse source radical times
its part in the target radical. -/
def firstChart :
    ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf (unipotentPoints ψ)) ×
        (unipotentPoints ψ ⊓ unipotentPoints χ : Subgroup (RationalPoint F G.X)) ≃ₜ
      unipotentPoints ψ :=
  ((Homeomorph.refl _).prodCongr
    (subgroupOfHomeomorphOfMem
      (unipotentPoints (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ Dynamic.inverseCocharacter χ))
      (unipotentPoints ψ) (unipotentPoints ψ ⊓ unipotentPoints χ) (fun g => by
        rw [inverse_inverseCocharacter]
        exact and_comm)).symm).trans
    (MatrixRepresentation.unipotentIntersectionProduct F (Dynamic.inverseCocharacter χ) ψ
      contractingUnit contractingUnit_tendsto
      (by
        rw [Dynamic.centralizer_inverseCocharacter]
        exact cocharPoint_mem_centralizer_left hZ _)
      (fun m hm hmU => by
        rw [Dynamic.centralizer_inverseCocharacter] at hm
        exact eq_one_of_mem_centralizer_left_of_mem_radical hZ hm hmU))

include hZ in
/-- The target radical splits as its part in the middle radical times its part in
the inverse middle radical. -/
def secondChart :
    ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)) ×
        (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
          Subgroup (RationalPoint F G.X)) ≃ₜ
      unipotentPoints χ :=
  ((Homeomorph.refl _).prodCongr
    (subgroupOfHomeomorphOfMem
      (unipotentPoints (Dynamic.inverseCocharacter ψ))
      (unipotentPoints χ)
      (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ)
      (fun _ => Iff.rfl)).symm).trans
    (MatrixRepresentation.unipotentIntersectionProduct F ψ χ
      contractingUnit contractingUnit_tendsto
      (cocharPoint_mem_centralizer_right hZ _)
      (fun _ hm hmU => eq_one_of_mem_centralizer_right_of_mem_radical hZ hm hmU))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The endpoint intersection of the inverse source radical with the target
radical has only the identity. -/
theorem inverseRadical_subgroupOf_eq_one
    (h : (unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf (unipotentPoints χ)) :
    h = 1 :=
  Subtype.ext (Subtype.ext
    (eq_one_of_mem_inverse_radical χ (Subgroup.mem_subgroupOf.mp h.property) h.val.property))

include hZ in
/-- The ordered chart datum for source radical `U(χ⁻¹)`, middle radical `U(ψ)`
and target radical `U(χ)`, where `χ` and `ψ` have the same Levi points. The
complements are `U(ψ) ∩ U(χ)` and `U(ψ⁻¹) ∩ U(χ)`. -/
def factorization :
    OrderedSubgroupFactorization (unipotentPoints (Dynamic.inverseCocharacter χ))
      (unipotentPoints ψ) (unipotentPoints χ)
      (unipotentPoints ψ ⊓ unipotentPoints χ)
      (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ) where
  first_le := inf_le_left
  first_le_target := inf_le_right
  second_le := inf_le_right
  first := firstChart hZ
  second := secondChart hZ
  composite := (trivialProdHomeomorph 1 inverseRadical_subgroupOf_eq_one).trans
    (((subgroupOfHomeomorphOfMem (unipotentPoints ψ) (unipotentPoints χ)
      (unipotentPoints ψ ⊓ unipotentPoints χ) (fun _ => Iff.rfl)).symm.prodCongr
        (Homeomorph.refl _)).trans (secondChart hZ))
  first_eq _ := rfl
  second_eq _ := rfl
  composite_eq p := by
    rw [inverseRadical_subgroupOf_eq_one p.1, OneMemClass.coe_one, one_mul]
    rfl

section Integral

open Aubert.General QuotientIntegration Haar OrderedSubgroupFactorization Induction

local instance standardIntertwiningOppositeChartsT2Space : T2Space F := BruhatTits.localField_t2Space F
local instance standardIntertwiningOppositeChartsIsTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance standardIntertwiningOppositeChartsT2Space2 : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance standardIntertwiningOppositeChartsLocallyCompactSpace : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance standardIntertwiningOppositeChartsNonarchimedeanGroup : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance standardIntertwiningOppositeChartsSecondCountableTopology : SecondCountableTopology F := localField_secondCountableTopology F
local instance standardIntertwiningOppositeChartsSecondCountableTopology2 : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G

variable (χ ψ) in
omit [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The first complement `U(ψ) ∩ U(χ)` is closed. -/
theorem firstComplement_isClosed :
    IsClosed ((unipotentPoints ψ ⊓ unipotentPoints χ : Subgroup (RationalPoint F G.X)) :
      Set (RationalPoint F G.X)) :=
  (isClosed_unipotentPoints ψ).inter (isClosed_unipotentPoints χ)

variable (χ ψ) in
omit [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The second complement `U(ψ⁻¹) ∩ U(χ)` is closed. -/
theorem secondComplement_isClosed :
    IsClosed ((unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
      Subgroup (RationalPoint F G.X)) : Set (RationalPoint F G.X)) :=
  (isClosed_unipotentPoints _).inter (isClosed_unipotentPoints χ)

variable (Q : OpenSubgroup (RationalPoint F G.X))
  (hQ : IsCompact (Q : Set (RationalPoint F G.X)))

include hZ in
/-- The middle local product identity holds automatically: the endpoint kernel
`U(χ⁻¹) ∩ U(χ)` is trivial and the nested complement is all of `U(ψ) ∩ U(χ)`. -/
theorem middle_localProduct :
    (factorization hZ).intersectionSubgroupProduct ''
      ({h : ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
          (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)) |
          h.val ∈ sourceMiddleCompactOpen Q (isClosed_unipotentPoints ψ)
            (isClosed_unipotentPoints χ)} ×ˢ
        ((factorization hZ).sourceNestedComplementCompactOpen Q
            (firstComplement_isClosed χ ψ) :
          Set (((unipotentPoints ψ ⊓ unipotentPoints χ :
            Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ)).subgroupOf
              ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))))) =
      (sourceMiddleCompactOpen Q (isClosed_unipotentPoints ψ) (isClosed_unipotentPoints χ) :
        Set ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))) := by
  ext x
  constructor
  · rintro ⟨⟨h, k⟩, ⟨hh, hk⟩, rfl⟩
    rw [intersectionSubgroupProduct_eq]
    exact (sourceMiddleCompactOpen Q (isClosed_unipotentPoints ψ)
      (isClosed_unipotentPoints χ)).mul_mem hh hk
  · intro hx
    have hV : (x.val : RationalPoint F G.X) ∈
        (unipotentPoints ψ ⊓ unipotentPoints χ : Subgroup (RationalPoint F G.X)) :=
      ⟨Subgroup.mem_subgroupOf.mp x.property, x.val.property⟩
    refine ⟨⟨1, ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hV)⟩⟩,
      ⟨?_, hx⟩, ?_⟩
    · exact (sourceMiddleCompactOpen Q (isClosed_unipotentPoints ψ)
        (isClosed_unipotentPoints χ)).one_mem
    · rw [intersectionSubgroupProduct_eq]
      simp

include hZ in
/-- The first local product identity follows from the ordered product
`Q ∩ U(ψ) = (Q ∩ U(χ⁻¹) ∩ U(ψ)) (Q ∩ U(ψ) ∩ U(χ))`. -/
theorem first_localProduct_of_hasCompactOpenProduct
    (hfac : HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
      (unipotentPoints (Dynamic.inverseCocharacter χ) ⊓ unipotentPoints ψ)
      (unipotentPoints ψ ⊓ unipotentPoints χ) (unipotentPoints ψ)) :
    (factorization hZ).firstSubgroupProduct ''
      ({h : (unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf (unipotentPoints ψ) |
          h.val ∈ sourceTargetCompactOpen Q (isClosed_unipotentPoints ψ)} ×ˢ
        ((factorization hZ).sourceFirstCompactOpen Q (firstComplement_isClosed χ ψ) :
          Set ((unipotentPoints ψ ⊓ unipotentPoints χ :
            Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints ψ)))) =
        (sourceTargetCompactOpen Q (isClosed_unipotentPoints ψ) : Set (unipotentPoints ψ)) := by
  ext x
  constructor
  · rintro ⟨⟨h, k⟩, ⟨hh, hk⟩, rfl⟩
    rw [firstSubgroupProduct_eq]
    exact (sourceTargetCompactOpen Q (isClosed_unipotentPoints ψ)).mul_mem hh hk
  · intro hx
    obtain ⟨a, ha, haQ, b, hb, hbQ, hab⟩ := hfac x.val x.property hx
    refine ⟨⟨⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.mpr ha.1⟩,
      ⟨⟨b, hb.1⟩, Subgroup.mem_subgroupOf.mpr hb⟩⟩, ⟨haQ, hbQ⟩, ?_⟩
    rw [firstSubgroupProduct_eq]
    exact Subtype.ext hab.symm

include hZ in
/-- The second local product identity follows from the ordered product
`Q ∩ U(χ) = (Q ∩ U(ψ) ∩ U(χ)) (Q ∩ U(ψ⁻¹) ∩ U(χ))`. -/
theorem second_localProduct_of_hasCompactOpenProduct
    (hfac : HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
      (unipotentPoints ψ ⊓ unipotentPoints χ)
      (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ)
      (unipotentPoints χ)) :
    (factorization hZ).secondSubgroupProduct ''
      ({h : (unipotentPoints ψ).subgroupOf (unipotentPoints χ) |
          h.val ∈ sourceTargetCompactOpen Q (isClosed_unipotentPoints χ)} ×ˢ
        ((factorization hZ).sourceSecondComplementCompactOpen Q
            (secondComplement_isClosed χ ψ) :
          Set ((unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
            Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ)))) =
        (sourceTargetCompactOpen Q (isClosed_unipotentPoints χ) : Set (unipotentPoints χ)) := by
  ext x
  constructor
  · rintro ⟨⟨h, k⟩, ⟨hh, hk⟩, rfl⟩
    rw [secondSubgroupProduct_eq]
    exact (sourceTargetCompactOpen Q (isClosed_unipotentPoints χ)).mul_mem hh hk
  · intro hx
    obtain ⟨a, ha, haQ, b, hb, hbQ, hab⟩ := hfac x.val x.property hx
    refine ⟨⟨⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.mpr ha.1⟩,
      ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb⟩⟩, ⟨haQ, hbQ⟩, ?_⟩
    rw [secondSubgroupProduct_eq]
    exact Subtype.ext hab.symm

section Composition

variable
  [MeasurableSpace (unipotentPoints ψ)] [BorelSpace (unipotentPoints ψ)]
  [MeasurableSpace (unipotentPoints χ)] [BorelSpace (unipotentPoints χ)]
  [MeasurableSpace ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints ψ))]
  [BorelSpace ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints ψ))]
  [MeasurableSpace ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))]
  [BorelSpace ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))]
  [MeasurableSpace ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints χ))]
  [BorelSpace ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints χ))]
  [MeasurableSpace (unipotentPoints ψ ⊓ unipotentPoints χ : Subgroup (RationalPoint F G.X))]
  [BorelSpace (unipotentPoints ψ ⊓ unipotentPoints χ : Subgroup (RationalPoint F G.X))]
  [MeasurableSpace (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X))]
  [BorelSpace (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X))]
  [MeasurableSpace ((unipotentPoints ψ ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints ψ))]
  [BorelSpace ((unipotentPoints ψ ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints ψ))]
  [MeasurableSpace (((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)))]
  [BorelSpace (((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)))]
  [MeasurableSpace (((unipotentPoints ψ ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ)).subgroupOf
      ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)))]
  [BorelSpace (((unipotentPoints ψ ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ)).subgroupOf
      ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)))]
  [MeasurableSpace ((unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ))]
  [BorelSpace ((unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ))]
  [MeasurableSpace (QuotientIntegration.LeftQuotient
    (((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
      (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))))]
  [BorelSpace (QuotientIntegration.LeftQuotient
    (((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
      (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))))]
  [MeasurableSpace (QuotientSpace (U := unipotentPoints (Dynamic.inverseCocharacter χ))
    (unipotentPoints ψ))]
  [BorelSpace (QuotientSpace (U := unipotentPoints (Dynamic.inverseCocharacter χ))
    (unipotentPoints ψ))]
  [MeasurableSpace (QuotientSpace (U := unipotentPoints ψ) (unipotentPoints χ))]
  [BorelSpace (QuotientSpace (U := unipotentPoints ψ) (unipotentPoints χ))]
  [MeasurableSpace (QuotientSpace (U := unipotentPoints (Dynamic.inverseCocharacter χ))
    (unipotentPoints χ))]
  [BorelSpace (QuotientSpace (U := unipotentPoints (Dynamic.inverseCocharacter χ))
    (unipotentPoints χ))]
  {P₀ P₁ M : Subgroup (RationalPoint F G.X)}
  (h₀ : IsSemidirectDecomposition P₀ M (unipotentPoints (Dynamic.inverseCocharacter χ)))
  (h₁ : IsSemidirectDecomposition P₁ M (unipotentPoints ψ))
  (A : Langlands.SmoothRep.{0, u, uV} ℂ M)

include hZ in
/-- **Standard-integral composition through a common-Levi middle radical.** For
an integral from the opposite of `P(χ)` to `P(ψ)` followed by one from `P(ψ)` to
`P(χ)`, at the source quotient measures normalized by one compact open `Q`, the
composite is the direct integral from the opposite of `P(χ)` to `P(χ)`. The
ordered charts and the middle local product identity are proved; the two outer
local product identities and ordered absolute convergence remain inputs. -/
theorem comp_hasIntegral
    (hlocal₀ : (factorization hZ).firstSubgroupProduct ''
      ({h : (unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf (unipotentPoints ψ) |
          h.val ∈ sourceTargetCompactOpen Q (isClosed_unipotentPoints ψ)} ×ˢ
        ((factorization hZ).sourceFirstCompactOpen Q (firstComplement_isClosed χ ψ) :
          Set ((unipotentPoints ψ ⊓ unipotentPoints χ :
            Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints ψ)))) =
        (sourceTargetCompactOpen Q (isClosed_unipotentPoints ψ) : Set (unipotentPoints ψ)))
    (hlocal₂ : (factorization hZ).secondSubgroupProduct ''
      ({h : (unipotentPoints ψ).subgroupOf (unipotentPoints χ) |
          h.val ∈ sourceTargetCompactOpen Q (isClosed_unipotentPoints χ)} ×ˢ
        ((factorization hZ).sourceSecondComplementCompactOpen Q
            (secondComplement_isClosed χ ψ) :
          Set ((unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
            Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ)))) =
        (sourceTargetCompactOpen Q (isClosed_unipotentPoints χ) : Set (unipotentPoints χ)))
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀
      (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))).obj A}
    {Φ : (DynamicNormalization.leviTwistedInductionFunctor h₁
      (isClosed_unipotentPoints ψ)).obj A}
    {J : RationalPoint F G.X → A}
    (hf : HasIntegral h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))
      (unipotentPoints ψ) A
      (DynamicSource.quotientMeasure Q hQ (Dynamic.inverseCocharacter χ) ψ) f
      (eval P₁ (leviInflatedInducingRepresentation h₁ (isClosed_unipotentPoints ψ) A) Φ))
    (hΦ : HasIntegral h₁ (isClosed_unipotentPoints ψ) (unipotentPoints χ) A
      (DynamicSource.quotientMeasure Q hQ ψ χ) Φ J)
    (ha : OrderedScalarIntegrable h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ)) A
      (subgroupCompactOpenHaar Q hQ _ (firstComplement_isClosed χ ψ))
      (subgroupCompactOpenHaar Q hQ _ (secondComplement_isClosed χ ψ)) f) :
    HasIntegral h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))
      (unipotentPoints χ) A
      (DynamicSource.quotientMeasure Q hQ (Dynamic.inverseCocharacter χ) χ) f J :=
  DynamicSource.comp_hasIntegral Q hQ (Dynamic.inverseCocharacter χ) ψ χ (factorization hZ)
    (firstComplement_isClosed χ ψ) (secondComplement_isClosed χ ψ)
    hlocal₀ (middle_localProduct hZ Q) hlocal₂ h₀ h₁ A hf hΦ ha

include hZ in
/-- The composition theorem with both outer local product identities replaced
by the two ordered compact-open products. -/
theorem comp_hasIntegral_of_hasCompactOpenProduct
    (hfac₀ : HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
      (unipotentPoints (Dynamic.inverseCocharacter χ) ⊓ unipotentPoints ψ)
      (unipotentPoints ψ ⊓ unipotentPoints χ) (unipotentPoints ψ))
    (hfac₂ : HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
      (unipotentPoints ψ ⊓ unipotentPoints χ)
      (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ)
      (unipotentPoints χ))
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀
      (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))).obj A}
    {Φ : (DynamicNormalization.leviTwistedInductionFunctor h₁
      (isClosed_unipotentPoints ψ)).obj A}
    {J : RationalPoint F G.X → A}
    (hf : HasIntegral h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))
      (unipotentPoints ψ) A
      (DynamicSource.quotientMeasure Q hQ (Dynamic.inverseCocharacter χ) ψ) f
      (eval P₁ (leviInflatedInducingRepresentation h₁ (isClosed_unipotentPoints ψ) A) Φ))
    (hΦ : HasIntegral h₁ (isClosed_unipotentPoints ψ) (unipotentPoints χ) A
      (DynamicSource.quotientMeasure Q hQ ψ χ) Φ J)
    (ha : OrderedScalarIntegrable h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ)) A
      (subgroupCompactOpenHaar Q hQ _ (firstComplement_isClosed χ ψ))
      (subgroupCompactOpenHaar Q hQ _ (secondComplement_isClosed χ ψ)) f) :
    HasIntegral h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))
      (unipotentPoints χ) A
      (DynamicSource.quotientMeasure Q hQ (Dynamic.inverseCocharacter χ) χ) f J :=
  comp_hasIntegral hZ Q hQ h₀ h₁ A
    (first_localProduct_of_hasCompactOpenProduct hZ Q hfac₀)
    (second_localProduct_of_hasCompactOpenProduct hZ Q hfac₂) hf hΦ ha

end Composition

end Integral

end OppositeCharts

end Langlands.Plancherel.StandardIntertwining
