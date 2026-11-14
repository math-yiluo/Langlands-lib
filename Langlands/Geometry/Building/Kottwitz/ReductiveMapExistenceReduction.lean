import Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedNaturalityReduction
import Langlands.Geometry.Building.Kottwitz.FundamentalGroupStatement
import Langlands.GroupScheme.ZExtensionExistenceStatement

/-! # Formal descent and independence for the reductive Kottwitz map -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [Normal k (UnramifiedClosure F)]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)

/-- The actual point homomorphism of a z-extension. -/
abbrev zExtensionPointMap (z : ZExtension G) :
    reductiveKPoints F k z.H →* reductiveKPoints F k G :=
  z.H.affinePointsTarget z.p (CommAlgCat.of k (UnramifiedClosure F))

/-- The homomorphism that must descend from the source of a z-extension. -/
def zExtensionKottwitzComposite (z : ZExtension G) :
    reductiveKPoints F k z.H →* Multiplicative (ReductiveTarget F k G hG) :=
  ((fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
    G hG z.H z.isZExtension.source_reductive z.p).toAddMonoidHom.toMultiplicative).comp
      (simplyConnectedDerivedKottwitz F k z.H z.isZExtension.source_reductive
        z.isZExtension.derived_simplyConnected)

omit [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [Normal k (UnramifiedClosure F)] in
/-- The kernel on coefficient points is precisely the image of the central torus. -/
theorem zExtensionPointMap_mem_ker_iff (z : ZExtension G)
    (x : reductiveKPoints F k z.H) :
    x ∈ (zExtensionPointMap F k G z).ker ↔
      ∃ t : reductiveKPoints F k z.Z.toGrp,
        affinePointsTarget z.Z.toGrp z.i (CommAlgCat.of k (UnramifiedClosure F)) t = x := by
  change x ≫ z.p.hom.hom = 1 ↔ ∃ t, t ≫ z.i.hom.hom = x
  rw [← mem_range_kernelι_iff, z.isZExtension.quotient.2.2.2,
    SubgroupFunctor.mem_range]

/-- The descent obstruction is exactly vanishing of the composite on central-torus points. -/
theorem zExtensionKottwitzComposite_kernel_iff (z : ZExtension G) :
    (zExtensionPointMap F k G z).ker ≤ (zExtensionKottwitzComposite F k G hG z).ker ↔
      ∀ t : reductiveKPoints F k z.Z.toGrp,
        zExtensionKottwitzComposite F k G hG z
          (affinePointsTarget z.Z.toGrp z.i (CommAlgCat.of k (UnramifiedClosure F)) t) = 1 := by
  constructor
  · intro h t
    exact h ((zExtensionPointMap_mem_ker_iff F k G z _).mpr ⟨t, rfl⟩)
  · intro h x hx
    obtain ⟨t, rfl⟩ := (zExtensionPointMap_mem_ker_iff F k G z x).mp hx
    exact h t

theorem zExtensionKottwitzLawAt_iff_comp (z : ZExtension G)
    (κ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)) :
    ZExtensionKottwitzLawAt F k G hG z κ ↔
      κ.comp (zExtensionPointMap F k G z) = zExtensionKottwitzComposite F k G hG z := by
  constructor
  · intro h
    exact MonoidHom.ext fun x => congrArg Multiplicative.ofAdd (h x)
  · intro h x
    exact congrArg Multiplicative.toAdd (congrArg (fun f => f x) h)

/-- A single point-surjective square determines its homomorphism. -/
theorem zExtensionKottwitzLawAt_ext (z : ZExtension G)
    (hp : Function.Surjective (zExtensionPointMap F k G z))
    {κ κ' : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)}
    (hκ : ZExtensionKottwitzLawAt F k G hG z κ)
    (hκ' : ZExtensionKottwitzLawAt F k G hG z κ') : κ = κ' := by
  ext y
  obtain ⟨x, rfl⟩ := hp y
  exact congrArg Multiplicative.ofAdd ((hκ x).trans (hκ' x).symm)

/-- Descent through one actual z-extension reduces to its point-map kernel. -/
theorem zExtensionKottwitzLawAt_existsUnique (z : ZExtension G)
    (hp : Function.Surjective (zExtensionPointMap F k G z))
    (hker : (zExtensionPointMap F k G z).ker ≤
      (zExtensionKottwitzComposite F k G hG z).ker) :
    ∃! κ, ZExtensionKottwitzLawAt F k G hG z κ := by
  let κ := (zExtensionPointMap F k G z).liftOfSurjective hp
    ⟨zExtensionKottwitzComposite F k G hG z, hker⟩
  have hκ : ZExtensionKottwitzLawAt F k G hG z κ := by
    apply (zExtensionKottwitzLawAt_iff_comp F k G hG z κ).mpr
    exact MonoidHom.liftOfRightInverse_comp _ _ _ _
  exact ⟨κ, hκ, fun κ' hκ' => zExtensionKottwitzLawAt_ext F k G hG z hp hκ' hκ⟩

theorem reductiveKottwitz_spec_of_exists
    (hex : ∃ κ, IsReductiveKottwitzHom F k G hG κ) :
    IsReductiveKottwitzHom F k G hG (reductiveKottwitz F k G hG) :=
  Classical.epsilon_spec hex

theorem isReductiveKottwitzHom_ext (z : ZExtension G)
    (hp : Function.Surjective (zExtensionPointMap F k G z))
    {κ κ' : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)}
    (hκ : IsReductiveKottwitzHom F k G hG κ)
    (hκ' : IsReductiveKottwitzHom F k G hG κ') : κ = κ' :=
  zExtensionKottwitzLawAt_ext F k G hG z hp (hκ.2 z) (hκ'.2 z)

theorem zExtensionKottwitzLawAt_iff_eq_reductiveKottwitz (z : ZExtension G)
    (hp : Function.Surjective (zExtensionPointMap F k G z))
    (hκ : IsReductiveKottwitzHom F k G hG (reductiveKottwitz F k G hG))
    (κ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)) :
    ZExtensionKottwitzLawAt F k G hG z κ ↔ κ = reductiveKottwitz F k G hG := by
  constructor
  · exact fun h => zExtensionKottwitzLawAt_ext F k G hG z hp h (hκ.2 z)
  · rintro rfl
    exact hκ.2 z

theorem zExtensionKottwitzLawAt_surjective (z : ZExtension G)
    {κ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)}
    (hκ : ZExtensionKottwitzLawAt F k G hG z κ)
    (hsource : Function.Surjective
      (simplyConnectedDerivedKottwitz F k z.H z.isZExtension.source_reductive
        z.isZExtension.derived_simplyConnected))
    (htarget : Function.Surjective
      (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
        G hG z.H z.isZExtension.source_reductive z.p)) : Function.Surjective κ := by
  intro y
  obtain ⟨a, ha⟩ := htarget y.toAdd
  obtain ⟨x, hx⟩ := hsource (Multiplicative.ofAdd a)
  refine ⟨zExtensionPointMap F k G z x, ?_⟩
  apply Multiplicative.toAdd.injective
  have h := hκ x
  rw [hx] at h
  exact h.trans ha

section Independence

variable [IsSepClosure k (SeparableClosure F)]

omit [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [Normal k (UnramifiedClosure F)] [IsSepClosure k (SeparableClosure F)] in
/-- Equality of point maps induced by a commuting triangle of group schemes. -/
theorem zExtensionPointMap_triangle (z w : ZExtension G) (r : w.H ⟶ z.H)
    (hr : r ≫ z.p = w.p) (x : reductiveKPoints F k w.H) :
    zExtensionPointMap F k G z
      (w.H.affinePointsTarget r (CommAlgCat.of k (UnramifiedClosure F)) x) =
      zExtensionPointMap F k G w x := by
  change (x ≫ r.hom.hom) ≫ z.p.hom.hom = x ≫ w.p.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, hr]

/-- A common z-extension compares two descended maps, using naturality only upstairs. -/
theorem zExtensionKottwitzLawAt_compare
    (hmap : FundamentalInertiaMapStatement.{u})
    (z z' w : ZExtension G)
    (r : w.H ⟶ z.H) (r' : w.H ⟶ z'.H)
    (hr : r ≫ z.p = w.p) (hr' : r' ≫ z'.p = w.p)
    (hw : Function.Surjective (zExtensionPointMap F k G w))
    (hn : SimplyConnectedDerivedKottwitzNaturalAt F k w.H z.H
      w.isZExtension.source_reductive z.isZExtension.source_reductive
      w.isZExtension.derived_simplyConnected z.isZExtension.derived_simplyConnected r)
    (hn' : SimplyConnectedDerivedKottwitzNaturalAt F k w.H z'.H
      w.isZExtension.source_reductive z'.isZExtension.source_reductive
      w.isZExtension.derived_simplyConnected z'.isZExtension.derived_simplyConnected r')
    {κ κ' : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)}
    (hκ : ZExtensionKottwitzLawAt F k G hG z κ)
    (hκ' : ZExtensionKottwitzLawAt F k G hG z' κ') : κ = κ' := by
  have hc := (hmap k (UnramifiedClosure F) (SeparableClosure F)).2.2
  have descend {v : ZExtension G} (s : w.H ⟶ v.H) (hs : s ≫ v.p = w.p)
      (hnat : SimplyConnectedDerivedKottwitzNaturalAt F k w.H v.H
        w.isZExtension.source_reductive v.isZExtension.source_reductive
        w.isZExtension.derived_simplyConnected v.isZExtension.derived_simplyConnected s)
      {κv : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)}
      (hκv : ZExtensionKottwitzLawAt F k G hG v κv) :
      ZExtensionKottwitzLawAt F k G hG w κv := by
    intro x
    rw [← zExtensionPointMap_triangle F k G v w s hs x]
    rw [hκv, hnat]
    have h := congrArg
      (fun f => f (simplyConnectedDerivedKottwitz F k w.H
        w.isZExtension.source_reductive w.isZExtension.derived_simplyConnected x).toAdd)
      (hc w.H v.H G w.isZExtension.source_reductive v.isZExtension.source_reductive hG
        s v.p)
    simpa only [LinearMap.comp_apply, hs] using h
  exact zExtensionKottwitzLawAt_ext F k G hG w hw
    (descend r hr hn hκ) (descend r' hr' hn' hκ')

/-- Complete construction at a fixed group from the remaining structural inputs.
No z-extension or square witness is an unconditional conclusion of this draft. -/
theorem reductiveKottwitzExistenceAt_of_structural_inputs
    (hsc : SimplyConnectedDerivedKottwitzStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hnat : ∀ (H J : GroupScheme (Spec (CommRingCat.of k)))
      (hH : IsConnectedReductive H) (hJ : IsConnectedReductive J)
      (hscH : HasSimplyConnectedDerivedGroup H) (hscJ : HasSimplyConnectedDerivedGroup J)
      (f : H ⟶ J),
      SimplyConnectedDerivedKottwitzNaturalAt F k H J hH hJ hscH hscJ f)
    (hz : Nonempty (ZExtension G))
    (hp : ∀ z : ZExtension G, Function.Surjective (zExtensionPointMap F k G z))
    (ht : ∀ z : ZExtension G, Function.Surjective
      (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
        G hG z.H z.isZExtension.source_reductive z.p))
    (hk : ∀ z : ZExtension G, (zExtensionPointMap F k G z).ker ≤
      (zExtensionKottwitzComposite F k G hG z).ker)
    (hrefine : ∀ z z' : ZExtension G, ∃ w : ZExtension G,
      ∃ r : w.H ⟶ z.H, ∃ r' : w.H ⟶ z'.H,
        r ≫ z.p = w.p ∧ r' ≫ z'.p = w.p) :
    Nonempty (ZExtension G) ∧
    (∃! κ, IsReductiveKottwitzHom F k G hG κ) ∧
    IsReductiveKottwitzHom F k G hG (reductiveKottwitz F k G hG) ∧
    Function.Surjective (reductiveKottwitz F k G hG) ∧
    (∀ hscG : HasSimplyConnectedDerivedGroup G,
      reductiveKottwitz F k G hG = simplyConnectedDerivedKottwitz F k G hG hscG) ∧
    ∀ z : ZExtension G,
      Function.Surjective (zExtensionPointMap F k G z) ∧
      Function.Surjective
        (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
          G hG z.H z.isZExtension.source_reductive z.p) ∧
      ∀ κ, ZExtensionKottwitzLawAt F k G hG z κ ↔ κ = reductiveKottwitz F k G hG := by
  obtain ⟨z⟩ := hz
  obtain ⟨κ, hκ, _⟩ := zExtensionKottwitzLawAt_existsUnique F k G hG z (hp z) (hk z)
  have hall : IsReductiveKottwitzHom F k G hG κ := by
    refine ⟨⟨z⟩, ?_⟩
    intro z'
    obtain ⟨κ', hκ', _⟩ :=
      zExtensionKottwitzLawAt_existsUnique F k G hG z' (hp z') (hk z')
    obtain ⟨w, r, r', hr, hr'⟩ := hrefine z z'
    have heq : κ = κ' := zExtensionKottwitzLawAt_compare F k G hG hmap
      z z' w r r' hr hr' (hp w)
      (hnat _ _ _ _ _ _ r) (hnat _ _ _ _ _ _ r') hκ hκ'
    simpa only [heq] using hκ'
  have hselected := reductiveKottwitz_spec_of_exists F k G hG ⟨κ, hall⟩
  refine ⟨⟨z⟩, ⟨κ, hall, ?_⟩, hselected, ?_, ?_, ?_⟩
  · intro κ' hκ'
    exact isReductiveKottwitzHom_ext F k G hG z (hp z) hκ' hall
  · exact zExtensionKottwitzLawAt_surjective F k G hG z (hselected.2 z)
      (hsc F k z.H z.isZExtension.source_reductive
        z.isZExtension.derived_simplyConnected).2.2.1 (ht z)
  · intro hscG
    exact zExtensionKottwitzLawAt_ext F k G hG z (hp z) (hselected.2 z)
      (hnat z.H G z.isZExtension.source_reductive hG
        z.isZExtension.derived_simplyConnected hscG z.p)
  · intro z'
    exact ⟨hp z', ht z',
      zExtensionKottwitzLawAt_iff_eq_reductiveKottwitz F k G hG z' (hp z') hselected⟩

end Independence

end Langlands.Geometry.Building.Kottwitz
