import Langlands.GroupScheme.Torus.MultiplicativeTypeConnectedActionStatement
import Langlands.GroupScheme.Torus.DiagonalizableRigidityStatement
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.GeometricConnectedness

/-! # Reduction of multiplicative-type actions to diagonalizable rigidity -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S S' : Scheme.{u}} {G H : GroupScheme S}

/-- Conjugation by the ambient group on a normal subgroup represented by a monomorphism. -/
def ofNormalSubgroup (i : H ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal) : AutomorphicAction G H :=
  ofNormalizedConjugation i (𝟙 G)
    (fun T g x _ hx => hn T g x (Subgroup.mem_top g) hx)

/-- The normal-subgroup action projects to the actual ambient conjugation. -/
theorem ofNormalSubgroup_act_comp (i : H ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal) {T : Over S}
    (g : T ⟶ G.X) (x : T ⟶ H.X) :
    (ofNormalSubgroup i hn).act g x ≫ i.hom.hom =
      g * (x ≫ i.hom.hom) * g⁻¹ := by
  simpa only [act, ofNormalSubgroup, ofNormalizedConjugation,
    Grp.id_hom_hom, Category.comp_id] using
    SubgroupFunctor.lift_comp_normalizedConjugation_comp i (𝟙 G)
      (fun T g x _ hx => hn T g x (Subgroup.mem_top g) hx) g x

/-- Triviality of the conjugation action implies all-refinement centrality. -/
theorem isCentral_of_normalSubgroup_act_eq (i : H ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal)
    (ha : ∀ (T : Over S) (g : T ⟶ G.X) (x : T ⟶ H.X),
      (ofNormalSubgroup i hn).act g x = x) : IsCentral i := by
  intro T x T' b g
  have he := ofNormalSubgroup_act_comp i hn g (b ≫ x)
  rw [ha] at he
  have hc := (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  change (b ≫ (x ≫ i.hom.hom)) * g = g * (b ≫ (x ≫ i.hom.hom))
  simpa only [Category.assoc] using hc

/-- A flat surjective change of base detects triviality on every scheme test. -/
theorem act_eq_self_of_baseChange (a : AutomorphicAction G H) (b : S' ⟶ S)
    [Flat b] [Surjective b]
    (ha : ∀ (T : Over S')
      (g : T ⟶ ((GroupScheme.baseChange b).obj G).X)
      (x : T ⟶ ((GroupScheme.baseChange b).obj H).X),
      (a.baseChange b).act g x = x)
    {T : Over S} (g : T ⟶ G.X) (x : T ⟶ H.X) : a.act g x = x := by
  let T' := (Over.pullback b).obj T
  let p : (Over.map b).obj T' ⟶ T :=
    Over.homMk (pullback.fst T.hom b) (by
      change pullback.fst T.hom b ≫ T.hom = pullback.snd T.hom b ≫ b
      exact pullback.condition)
  have : Epi p.left := by
    change Epi (pullback.fst T.hom b)
    exact Flat.epi_of_flat_of_surjective _
  have : Epi p := Over.epi_of_epi_left p
  apply (cancel_epi p).mp
  let g' := (baseChangePointsEquiv b G T').symm (p ≫ g)
  let x' := (baseChangePointsEquiv b H T').symm (p ≫ x)
  have he := congrArg (baseChangePointsEquiv b H T') (ha T' g' x')
  rw [baseChangePointsEquiv_act] at he
  simpa only [g', x', MulEquiv.apply_symm_apply, naturality] using he

end AutomorphicAction

/-- Diagonalizable rigidity makes every action on a diagonalizable group trivial. -/
theorem diagonalizableAction_eq_self_of_rigidity
    (hr : DiagonalizableRigidityStatement.{u})
    {k : Type u} [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (hH : Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp))
    (a : AutomorphicAction G H) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (x : T ⟶ H.X) : a.act g x = x := by
  have he := hr k H H Λ Λ inferInstance inferInstance hH hH G.X
    inferInstance inferInstance inferInstance a.hom
    (fun _ h y z => a.mul_right h y z)
    (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) T g x
  change lift g x ≫ a.hom = x
  simpa only [MonObj.comp_one, a.one_left] using he

/-- Splitting and flat-surjective reflection extend diagonalizable rigidity to every
finite-type group of multiplicative type and every connected algebraic acting group. -/
theorem multiplicativeTypeAction_eq_self_of_rigidity
    (hr : DiagonalizableRigidityStatement.{u})
    {k : Type u} [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (hH : IsMultiplicativeType H) (a : AutomorphicAction G H)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    a.act g x = x := by
  obtain ⟨K, hK, aK, Λ, hΛ, hFG, hsplit⟩ := hH
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hfpqc := fieldExtension_fpqc k K
  let : Surjective b := hfpqc.1
  let : Flat b := hfpqc.2.1
  let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_connected b
  let : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  let : QuasiCompact ((GroupScheme.baseChange b).obj G).X.hom := by
    change QuasiCompact (pullback.snd G.X.hom b)
    infer_instance
  apply a.act_eq_self_of_baseChange b _ g x
  intro V h y
  exact diagonalizableAction_eq_self_of_rigidity hr
    ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj H) Λ
    hsplit (a.baseChange b) h y

/-- The full connected-action and normal-centrality statement follows from the
unchanged diagonalizable rigidity statement. -/
theorem multiplicativeTypeConnectedAction_of_diagonalizableRigidity
    (hr : DiagonalizableRigidityStatement.{u}) :
    MultiplicativeTypeConnectedActionStatement.{u} := by
  intro k _ G H hft hqc hconn hH
  let : LocallyOfFiniteType G.X.hom := hft
  let : QuasiCompact G.X.hom := hqc
  let : ConnectedSpace G.X.left := hconn
  have hact := multiplicativeTypeAction_eq_self_of_rigidity hr G H hH
  refine ⟨fun a _ g x => hact a g x, ?_⟩
  intro i hi hn
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := by
    apply Over.mono_of_mono_left
  exact AutomorphicAction.isCentral_of_normalSubgroup_act_eq i hn
    (fun _ g x => hact (AutomorphicAction.ofNormalSubgroup i hn) g x)

end Langlands.GroupScheme
