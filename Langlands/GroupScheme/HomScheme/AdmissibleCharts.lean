import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.HomScheme.TorusSubgroupCharts
import Mathlib.AlgebraicGeometry.Sites.Representability

/-! # Actual open charts of the admissible-subgroup presheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli.OpenCharts

variable {S : Scheme.{u}} {G : GroupScheme S}
variable {U : Over S} {K : GroupScheme U.left}
variable (j : K ⟶ (baseChange U.hom).obj G) (hj : IsOpenChart j)

/-- The small section given by the actual chart family. -/
def sectionValue : (smallAdmissiblePresheaf G).obj (op U) :=
  (smallAdmissibleEquiv G U).symm
    ⟨SubgroupFunctor.range j, isAdmissible_range j hj.isClosedSubgroup hj.isTorus⟩

/-- The actual chart family induces a map to the total presheaf. -/
def chartMap : yoneda.obj U.left ⟶ totalAdmissiblePresheaf G :=
  yonedaEquiv.symm (Functor.OverTotal.ofFibre U (sectionValue j hj))

private theorem map_ofFibre {P : (Over S)ᵒᵖ ⥤ Type u}
    {T M : Over S} (a : T ⟶ M) (x : P.obj (op M)) :
    P.overTotal.map a.left.op (Functor.OverTotal.ofFibre M x) =
      Functor.OverTotal.ofFibre T (P.map a.op x) := by
  have hb : (P.overTotal.map a.left.op (Functor.OverTotal.ofFibre M x)).1 =
      T.hom := by
    rw [Functor.overTotal_map_fst, Functor.OverTotal.ofFibre_fst]
    exact Over.w a
  calc
    _ = Functor.OverTotal.ofFibre T
        (Functor.OverTotal.toFibre T
          (P.overTotal.map a.left.op (Functor.OverTotal.ofFibre M x)) hb) :=
      (Functor.OverTotal.ofFibre_toFibre T _ hb).symm
    _ = Functor.OverTotal.ofFibre T
        (P.map a.op (Functor.OverTotal.toFibre M
          (Functor.OverTotal.ofFibre M x) rfl)) :=
      congrArg _ (Functor.OverTotal.toFibre_naturality a _ rfl hb)
    _ = _ := congrArg (fun z => Functor.OverTotal.ofFibre T (P.map a.op z))
      (Functor.OverTotal.toFibre_ofFibre M x)

/-- A chart map evaluates the original actual family on every relative test. -/
theorem chartMap_app_of_over {T : Over S} (a : T ⟶ U) :
    (chartMap j hj).app (op T.left) a.left =
      Functor.OverTotal.ofFibre T
        ((smallAdmissibleEquiv G T).symm
          ⟨evaluate j a, isAdmissible_evaluate j hj.isClosedSubgroup hj.isTorus a⟩) := by
  change (smallAdmissiblePresheaf G).overTotal.map a.left.op
    (Functor.OverTotal.ofFibre U (sectionValue j hj)) = _
  rw [map_ofFibre]
  apply congrArg (Functor.OverTotal.ofFibre T)
  apply (smallAdmissibleEquiv G T).injective
  rw [smallAdmissibleEquiv_map, Equiv.apply_symm_apply]
  apply Subtype.ext
  exact restrict_eq_evaluate _ j (by simp only [sectionValue, Equiv.apply_symm_apply]) a

/-- Equality with a chart value is equality with its actual all-test evaluation. -/
theorem chartMap_app_eq_iff {T : Over S} (a : T ⟶ U)
    (ξ : (totalAdmissiblePresheaf G).obj (op T.left)) (hξ : ξ.1 = T.hom) :
    (chartMap j hj).app (op T.left) a.left = ξ ↔
      evaluate j a =
        (smallAdmissibleEquiv G T (Functor.OverTotal.toFibre T ξ hξ)).val := by
  rw [chartMap_app_of_over]
  constructor
  · intro h
    have h' := Functor.OverTotal.toFibre_congr T h rfl hξ
    rw [Functor.OverTotal.toFibre_ofFibre] at h'
    have h'' := congrArg (fun z => (smallAdmissibleEquiv G T z).val) h'
    simpa only [Equiv.apply_symm_apply] using h''
  · intro h
    rw [← Functor.OverTotal.ofFibre_toFibre T ξ hξ]
    apply congrArg (Functor.OverTotal.ofFibre T)
    apply (smallAdmissibleEquiv G T).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext h

/-- A chart value retains its actual structural morphism to the base. -/
theorem chartMap_app_fst {T : Scheme.{u}} (a : T ⟶ U.left) :
    ((chartMap j hj).app (op T) a).1 = a ≫ U.hom := rfl

/-- Injectivity of actual evaluation implies injectivity of the total chart map. -/
theorem chartMap_app_injective (T : Scheme.{u}) :
    Function.Injective ((chartMap j hj).app (op T)) := by
  intro a b hab
  have hbase : a ≫ U.hom = b ≫ U.hom := congrArg Sigma.fst hab
  let A : Over S := Over.mk (b ≫ U.hom)
  let a' : A ⟶ U := Over.homMk a hbase
  let b' : A ⟶ U := Over.homMk b rfl
  change (chartMap j hj).app (op A.left) a'.left =
    (chartMap j hj).app (op A.left) b'.left at hab
  rw [chartMap_app_of_over, chartMap_app_of_over] at hab
  have hf := Functor.OverTotal.toFibre_congr A hab rfl rfl
  rw [Functor.OverTotal.toFibre_ofFibre, Functor.OverTotal.toFibre_ofFibre] at hf
  have he : evaluate j a' = evaluate j b' := by
    simpa only [Equiv.apply_symm_apply] using
      congrArg (fun z => (smallAdmissibleEquiv G A z).val) hf
  exact congrArg (fun f => f.left) (hj.injective A a' b' he)

/-- Decode a total section as its actual admissible subgroup over its base map. -/
def actualSubgroup {T : Scheme.{u}}
    (ξ : (totalAdmissiblePresheaf G).obj (op T)) :
    AdmissibleSubgroup ((baseChange ξ.1).obj G) :=
  smallAdmissibleEquiv G (Over.mk ξ.1)
    (Functor.OverTotal.toFibre (Over.mk ξ.1) ξ rfl)

/-- Decoding a total restriction gives the actual family restriction. -/
theorem actualSubgroup_map {T T' : Scheme.{u}} (b : T' ⟶ T)
    (ξ : (totalAdmissiblePresheaf G).obj (op T)) :
    actualSubgroup ((totalAdmissiblePresheaf G).map b.op ξ) =
      restrict (Over.homMk b rfl : Over.mk (b ≫ ξ.1) ⟶ Over.mk ξ.1)
        (actualSubgroup ξ) := by
  let a : Over.mk (b ≫ ξ.1) ⟶ Over.mk ξ.1 := Over.homMk b rfl
  change smallAdmissibleEquiv G (Over.mk (b ≫ ξ.1))
    (Functor.OverTotal.toFibre (Over.mk (b ≫ ξ.1))
      ((totalAdmissiblePresheaf G).map b.op ξ) rfl) = _
  calc
    _ = smallAdmissibleEquiv G (Over.mk (b ≫ ξ.1))
        ((smallAdmissiblePresheaf G).map a.op
          (Functor.OverTotal.toFibre (Over.mk ξ.1) ξ rfl)) :=
      congrArg (smallAdmissibleEquiv G (Over.mk (b ≫ ξ.1)))
        (Functor.OverTotal.toFibre_naturality a ξ rfl rfl)
    _ = _ := smallAdmissibleEquiv_map a _

set_option maxHeartbeats 800000 in
/-- The chart lifting condition over a total section is represented by an
actual open subscheme, on every scheme test. -/
theorem exists_open_pullback {T : Scheme.{u}}
    (ξ : (totalAdmissiblePresheaf G).obj (op T)) :
    ∃ V : T.Opens, ∀ (T' : Scheme.{u}) (b : T' ⟶ T),
      (∃ a : T' ⟶ U.left,
        (chartMap j hj).app (op T') a =
          (totalAdmissiblePresheaf G).map b.op ξ) ↔ Set.range b.base ⊆ V := by
  let M : Over S := Over.mk ξ.1
  let F : AdmissibleSubgroup ((baseChange M.hom).obj G) := actualSubgroup ξ
  let r : AdmissibleRepresentative F := admissibleRepresentative F
  obtain ⟨V, hV⟩ := hj.isOpen M r.group r.hom r.closed r.torus
  refine ⟨V, ?_⟩
  intro T' b
  let A : Over S := Over.mk (b ≫ ξ.1)
  let b' : A ⟶ M := Over.homMk b rfl
  have he : (actualSubgroup ((totalAdmissiblePresheaf G).map b.op ξ)).val =
      evaluate r.hom b' := by
    calc
      _ = (restrict b' F).val := congrArg Subtype.val (actualSubgroup_map b ξ)
      _ = _ := restrict_eq_evaluate F r.hom r.represents.2 b'
  constructor
  · rintro ⟨a, ha⟩
    have habase : a ≫ U.hom = A.hom := congrArg Sigma.fst ha
    let a' : A ⟶ U := Over.homMk a habase
    have hea : evaluate j a' = evaluate r.hom b' :=
      ((chartMap_app_eq_iff j hj a' _ rfl).mp ha).trans he
    exact (hV A b').mp ⟨a', hea⟩
  · intro hb
    obtain ⟨a, ha⟩ := (hV A b').mpr hb
    refine ⟨a.left, (chartMap_app_eq_iff j hj a _ rfl).mpr ?_⟩
    exact ha.trans he.symm

theorem chartMap_app_comp {T T' : Scheme.{u}} (b : T' ⟶ T) (a : T ⟶ U.left) :
    (chartMap j hj).app (op T') (b ≫ a) =
      (totalAdmissiblePresheaf G).map b.op ((chartMap j hj).app (op T) a) := by
  change (totalAdmissiblePresheaf G).map (b ≫ a).op _ =
    (totalAdmissiblePresheaf G).map b.op ((totalAdmissiblePresheaf G).map a.op _)
  rw [op_comp, Functor.map_comp_apply]

set_option maxHeartbeats 800000 in
/-- An actual open chart is a relatively representable open immersion into
the total presheaf. -/
theorem isOpenImmersion_presheaf : IsOpenImmersion.presheaf (chartMap j hj) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let ξ := yonedaEquiv g
  have hg : ∀ {T' : Scheme.{u}} (a : T' ⟶ T),
      g.app (op T') a = (totalAdmissiblePresheaf G).map a.op ξ :=
    fun a => (map_yonedaEquiv g a).symm
  obtain ⟨V, hV⟩ := exists_open_pullback j hj ξ
  obtain ⟨φ, hφ⟩ := (hV V V.ι).mpr (by rw [Scheme.Opens.range_ι])
  refine ⟨V, yoneda.map φ, V.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨T'⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext c
    change (chartMap j hj).app (op T') (c ≫ φ) = g.app (op T') (c ≫ V.ι)
    rw [chartMap_app_comp, hφ, hg, op_comp, Functor.map_comp_apply]
  · rintro c c' ⟨-, h₂⟩
    exact (cancel_mono V.ι).mp h₂
  · intro x₂ x₃ hx
    change T' ⟶ U.left at x₂
    change T' ⟶ T at x₃
    change (chartMap j hj).app (op T') x₂ = g.app (op T') x₃ at hx
    have hrange : Set.range x₃.base ⊆ Set.range V.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact (hV T' x₃).mp ⟨x₂, hx.trans (hg x₃)⟩
    refine ⟨IsOpenImmersion.lift V.ι x₃ hrange, ?_,
      IsOpenImmersion.lift_fac V.ι x₃ hrange⟩
    change IsOpenImmersion.lift V.ι x₃ hrange ≫ φ = x₂
    apply chartMap_app_injective j hj T'
    rw [chartMap_app_comp, hφ, ← Functor.map_comp_apply, ← op_comp,
      IsOpenImmersion.lift_fac, ← hg]
    exact hx.symm

end Langlands.GroupScheme.TorusSubgroupModuli.OpenCharts
