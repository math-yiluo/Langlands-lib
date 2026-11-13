import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralSheafClassTwistStatement
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralRigidifiedComparison
import Langlands.AlgebraicGeometry.Picard.RigidifiedForgetLocallySurjective
import Langlands.AlgebraicGeometry.Picard.AffineLineBundlePicard

/-! # Proof: fppf Picard classes of a proper flat integral family with a section -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace ProperFlatIntegralSheafClassTwist

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The set-valued sheaf class factors through the abelian-group sheafification. -/
lemma sheafClassOf_eq_forgetSheafIso (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) :
    RelativePicard.sheafClassOf f T L =
      (RelativePicard.forgetSheafIso f).hom.app (op T)
        ((RelativePicard.toSheaf f).app (op T) (RelativePicard.classOf f T L)) := by
  have := congrArg (fun η => η.app (op T) (RelativePicard.classOf f T L))
    (RelativePicard.toSheaf_forgetSheafIso_hom f)
  exact this.symm

/-- Equality of set-valued sheaf classes is equality in the abelian-group sheaf. -/
lemma sheafClassOf_eq_iff (T : Over S) (L L' : LineBundle ((relativeSpace f).obj T)) :
    RelativePicard.sheafClassOf f T L = RelativePicard.sheafClassOf f T L' ↔
      (RelativePicard.toSheaf f).app (op T) (RelativePicard.classOf f T L) =
        (RelativePicard.toSheaf f).app (op T) (RelativePicard.classOf f T L') := by
  rw [sheafClassOf_eq_forgetSheafIso, sheafClassOf_eq_forgetSheafIso]
  have hinj : Function.Injective ((RelativePicard.forgetSheafIso f).hom.app (op T)) :=
    ((RelativePicard.forgetSheafIso f).app (op T)).toEquiv.injective
  exact hinj.eq_iff

/-- The class of `g^* N` restricts to zero along every base change on which `N` becomes
trivial in the Picard group. -/
lemma map_classOf_pullback_projection {T T' : Over S} (k : T' ⟶ T) (N : LineBundle T.left)
    (hk : Group.pullback k.left N.classOf = 0) :
    Group.pullback ((relativeSpace f).map k)
        (RelativePicard.classOf f T
          ((LineBundle.pullback ((relativeProjection f).app T)).obj N)) = 0 := by
  rw [RelativePicard.classOf, ← Group.pullback_lineBundle_classOf, ← AddMonoidHom.comp_apply, ← Group.pullback_comp,
    (relativeProjection f).naturality k, Group.pullback_comp, AddMonoidHom.comp_apply]
  simp only [Over.forget_map]
  rw [hk, map_zero]

/-- A line bundle pulled back from the base has the class of the trivial bundle in the fppf
Picard class sheaf: it is Zariski locally trivial and the sheaf is separated. -/
lemma sheafClassOf_pullback_projection (T : Over S) (N : LineBundle T.left) :
    RelativePicard.sheafClassOf f T
        ((LineBundle.pullback ((relativeProjection f).app T)).obj N) =
      RelativePicard.sheafClassOf f T (LineBundle.trivial ((relativeSpace f).obj T)) := by
  have hloc : ∀ (T' : Over S) (k : T' ⟶ T), Group.pullback k.left N.classOf = 0 →
      (RelativePicard.classSheafPresheaf f).map k.op
          (RelativePicard.sheafClassOf f T
            ((LineBundle.pullback ((relativeProjection f).app T)).obj N)) =
        (RelativePicard.classSheafPresheaf f).map k.op
          (RelativePicard.sheafClassOf f T (LineBundle.trivial ((relativeSpace f).obj T))) := by
    intro T' k hk
    have e1 := (RelativePicard.toClassSheaf f).naturality_apply k.op
      (RelativePicard.classOf f T ((LineBundle.pullback ((relativeProjection f).app T)).obj N))
    have e2 := (RelativePicard.toClassSheaf f).naturality_apply k.op
      (RelativePicard.classOf f T (LineBundle.trivial ((relativeSpace f).obj T)))
    dsimp only [RelativePicard.sheafClassOf]
    refine e1.symm.trans (Eq.trans ?_ e2)
    congr 1
    change Group.pullback ((relativeSpace f).map k) (RelativePicard.classOf f T _) =
      Group.pullback ((relativeSpace f).map k) (RelativePicard.classOf f T _)
    rw [map_classOf_pullback_projection f k N hk, RelativePicard.classOf_trivial, map_zero]
  have hpt : ∀ y : T.left, Group.pullback (N.trivializingOpen y).ι N.classOf = 0 := by
    intro y
    rw [Group.pullback_lineBundle_classOf,
      ← LineBundle.classOf_trivial (N.trivializingOpen y).toScheme]
    exact (LineBundle.classOf_eq_iff _ _).2
      ⟨((Scheme.Modules.restrictFunctorIsoPullback (N.trivializingOpen y).ι).app N.obj).symm ≪≫
        N.localTrivialization y⟩
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 (RelativePicard.classSheafPresheaf_isSheaf f)
  let E : Sieve T := Presheaf.equalizerSieve (F := RelativePicard.classSheafPresheaf f) (X := op T)
    (RelativePicard.sheafClassOf f T
      ((LineBundle.pullback ((relativeProjection f).app T)).obj N))
    (RelativePicard.sheafClassOf f T (LineBundle.trivial ((relativeSpace f).obj T)))
  have hE : E ∈ (Scheme.zariskiTopology.over S) T := by
    let 𝒰 : T.left.OpenCover :=
      T.left.openCoverOfIsOpenCover N.trivializingOpen
        (by
          apply TopologicalSpace.IsOpenCover.mk
          apply top_le_iff.mp
          intro x _
          exact (le_iSup N.trivializingOpen x) (N.mem_trivializingOpen x))
    rw [GrothendieckTopology.mem_over_iff]
    apply Scheme.mem_grothendieckTopology_iff.mpr
    refine ⟨𝒰, ?_⟩
    rintro V h ⟨x⟩
    rw [Sieve.overEquiv_iff]
    exact hloc _
      (Over.homMk (U := Over.mk ((N.trivializingOpen x).ι ≫ T.hom)) (N.trivializingOpen x).ι)
      (hpt x)
  have hE' : E ∈ (Scheme.fppfTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff] at hE ⊢
    exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hE
  exact (hsheaf.isSeparated E hE').ext (fun _ k hk => hk)

/-- The fppf sheafification unit at `T`, as a homomorphism out of the Picard group of
`T ×_S X`. -/
def unitHom (T : Over S) :
    Group ((relativeSpace f).obj T) →+ (RelativePicard.sheafPresheaf f).obj (op T) :=
  ((RelativePicard.toSheaf f).app (op T)).hom

/-- Equality of fppf sheaf classes, in terms of the homomorphism `unitHom`. -/
lemma sheafClassOf_eq_iff_unitHom (T : Over S) (L L' : LineBundle ((relativeSpace f).obj T)) :
    RelativePicard.sheafClassOf f T L = RelativePicard.sheafClassOf f T L' ↔
      unitHom f T (RelativePicard.classOf f T L) = unitHom f T (RelativePicard.classOf f T L') :=
  sheafClassOf_eq_iff f T L L'

/-- Group form: a line bundle pulled back from the base dies in the fppf Picard sheaf. -/
lemma unitHom_classOf_pullback_projection (T : Over S) (N : LineBundle T.left) :
    unitHom f T (RelativePicard.classOf f T
      ((LineBundle.pullback ((relativeProjection f).app T)).obj N)) = 0 := by
  rw [(sheafClassOf_eq_iff_unitHom f T _ _).1 (sheafClassOf_pullback_projection f T N),
    RelativePicard.classOf_trivial, map_zero]

/-- A line bundle is an invertible module in the sense of the ported definition. -/
lemma isInvertible_lineBundle {Y : Scheme.{u}} (N : LineBundle Y) :
    Scheme.Modules.IsInvertible N.obj :=
  ⟨fun x => by
    obtain ⟨U, hx, ⟨e⟩⟩ := N.property x
    exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N.obj).symm ≪≫ e⟩⟩⟩

/-- An invertible module in the sense of the ported definition is a line bundle. -/
def lineBundleOfIsInvertible {Y : Scheme.{u}} (N : Y.Modules)
    (hN : Scheme.Modules.IsInvertible N) : LineBundle Y :=
  ⟨N, fun x => by
    obtain ⟨U, hx, ⟨e⟩⟩ := hN.exists_trivialization x
    exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫ e⟩⟩⟩

end ProperFlatIntegralSheafClassTwist

open ProperFlatIntegralSheafClassTwist in
/-- Kleiman's description of the fppf Picard classes of a proper flat family with
geometrically integral fibres and a section. -/
theorem properFlatIntegralSheafClassTwist : ProperFlatIntegralSheafClassTwistStatement.{u} := by
  intro S X f hP hF hL hG hε' T
  obtain ⟨ε, hε⟩ := hε'
  have := hP
  have := hF
  have := hL
  have := hG
  let Θ := RigidifiedLineBundle.properFlatIntegralClassIso f ε hε
  have hinj : Function.Injective
      ((RigidifiedLineBundle.toClassPicardSheaf f ε hε).app (op T)) := fun a b hab => by
    have ha := types_congr_hom (Θ.hom_inv_id_app (op T)) a
    have hb := types_congr_hom (Θ.hom_inv_id_app (op T)) b
    rw [types_comp_apply, types_id_apply] at ha hb
    rw [← ha, ← hb]
    exact congrArg (Θ.inv.app (op T)) hab
  let g := (relativeProjection f).app T
  refine ⟨fun ξ => ?_, fun L L' => ⟨fun h => ?_, fun ⟨N, hN, ⟨e⟩⟩ => ?_⟩⟩
  · obtain ⟨r, hr⟩ := Quotient.exists_rep (Θ.inv.app (op T) ξ)
    refine ⟨(RigidifiedLineBundle.forget _).obj r, ?_⟩
    change Θ.hom.app (op T) (RigidifiedLineBundle.classOf f ε hε r) = ξ
    rw [show RigidifiedLineBundle.classOf f ε hε r = Θ.inv.app (op T) ξ from hr]
    exact types_congr_hom (Θ.inv_hom_id_app (op T)) ξ
  · rw [sheafClassOf_eq_iff_unitHom] at h
    let σ := (relativeSection f ε hε).app T
    let d : Group ((relativeSpace f).obj T) :=
      -RelativePicard.classOf f T L' + RelativePicard.classOf f T L
    let n : Group T.left := Group.pullback σ d
    let N : LineBundle T.left := Group.lineBundleRepresentative _ n
    let d₀ : Group ((relativeSpace f).obj T) := d - Group.pullback g n
    let M₀ : LineBundle ((relativeSpace f).obj T) := Group.lineBundleRepresentative _ d₀
    have hgN : RelativePicard.classOf f T ((LineBundle.pullback g).obj N) = Group.pullback g n := by
      rw [RelativePicard.classOf, ← Group.pullback_lineBundle_classOf]
      exact congrArg _ (Group.classOf_lineBundleRepresentative _ n)
    have hσ : Group.pullback σ d₀ = 0 := by
      have hσg : Group.pullback σ (Group.pullback g n) = n := by
        rw [← AddMonoidHom.comp_apply, ← Group.pullback_comp]
        have : σ ≫ g = 𝟙 T.left := relativeSection_projection f ε hε T
        rw [this]
        exact DFunLike.congr_fun (Group.pullback_id T.left) n
      change Group.pullback σ (d - Group.pullback g n) = 0
      rw [map_sub, hσg]
      exact sub_self _
    have hτ : unitHom f T d₀ = 0 := by
      change unitHom f T
        (-RelativePicard.classOf f T L' + RelativePicard.classOf f T L - Group.pullback g n) = 0
      rw [map_sub, map_add, map_neg, h, ← hgN, unitHom_classOf_pullback_projection,
        neg_add_cancel, sub_zero]
    have hM₀σ : ((LineBundle.pullback σ).obj M₀).classOf =
        (LineBundle.trivial T.left).classOf := by
      rw [← Group.pullback_lineBundle_classOf, Group.classOf_lineBundleRepresentative, hσ,
        LineBundle.classOf_trivial]
    obtain ⟨α⟩ := (LineBundle.classOf_eq_iff _ _).1 hM₀σ
    let R₀ : RigidifiedLineBundle.relative f ε hε T :=
      RigidifiedLineBundle.ofLineBundle M₀ α.symm
    have hR : RigidifiedLineBundle.classOf f ε hε R₀ =
        RigidifiedLineBundle.classOf f ε hε (RigidifiedLineBundle.trivial σ) := by
      apply hinj
      rw [RigidifiedLineBundle.toClassPicardSheaf_app_classOf,
        RigidifiedLineBundle.toClassPicardSheaf_app_classOf, sheafClassOf_eq_iff_unitHom]
      change unitHom f T (Group.lineBundleRepresentative _ d₀).classOf =
        unitHom f T (LineBundle.trivial _).classOf
      rw [Group.classOf_lineBundleRepresentative, hτ, LineBundle.classOf_trivial, map_zero]
    obtain ⟨eR⟩ := Quotient.exact hR
    have hc0 : d₀ = 0 := by
      rw [← Group.classOf_lineBundleRepresentative _ d₀,
        ← LineBundle.classOf_trivial ((relativeSpace f).obj T)]
      exact (LineBundle.classOf_eq_iff_iso _ _).2 ⟨(RigidifiedLineBundle.forget _).mapIso eR⟩
    have hcL : RelativePicard.classOf f T L = RelativePicard.classOf f T
        (LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso L'
          ((LineBundle.pullback g).obj N)) := by
      rw [RelativePicard.classOf_tensor, hgN]
      have hc0' : d - Group.pullback g n = 0 := hc0
      have hd : -RelativePicard.classOf f T L' + RelativePicard.classOf f T L =
          Group.pullback g n := sub_eq_zero.1 hc0'
      exact neg_add_eq_iff_eq_add.1 hd
    obtain ⟨eL⟩ := (LineBundle.classOf_eq_iff L
      (LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso L'
        ((LineBundle.pullback g).obj N))).1 hcL
    exact ⟨N.obj, isInvertible_lineBundle N,
      ⟨eL ≪≫ (portedTensorExplicitIso L'.obj ((Scheme.Modules.pullback g).obj N.obj)).symm⟩⟩
  · let N' : LineBundle T.left := lineBundleOfIsInvertible N hN
    let P := LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso L'
      ((LineBundle.pullback g).obj N')
    have hLP : RelativePicard.classOf f T L = RelativePicard.classOf f T P :=
      (LineBundle.classOf_eq_iff L P).2 ⟨e ≪≫ portedTensorExplicitIso _ _⟩
    rw [sheafClassOf_eq_iff_unitHom, hLP, RelativePicard.classOf_tensor, map_add,
      unitHom_classOf_pullback_projection, add_zero]

end Langlands.AlgebraicGeometry.Picard
