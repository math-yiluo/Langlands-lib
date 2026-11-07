import Langlands.GroupScheme.Descent.PullHomCoherence
import Langlands.GroupScheme.Descent.TripleComponents

/-! # Actual descent from a coherent semilinear family -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

namespace Langlands.GroupScheme.Descent

theorem pullHom_congr_map {S T U : Scheme.{u}} {q q' : U ⟶ T}
    (hq : q = q') {f g : T ⟶ S} {r s : U ⟶ S}
    {hf : q ≫ f = r} {hg : q ≫ g = s}
    (hf' : q' ≫ f = r) (hg' : q' ≫ g = s) {G H : GroupScheme S}
    (a : (baseChange f).obj G ⟶ (baseChange g).obj H) :
    pullHom q hf hg a = pullHom q' hf' hg' a := by
  subst q'
  rfl

/-- The identity comparison commutes with arbitrary actual pullback. -/
theorem baseChangeIdIso_comparison {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) :
    (baseChange b).mapIso (baseChangeIdIso G) =
      pullbackComparison (𝟙 S) b b (Category.comp_id _) G := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change _ ≫ pullback.fst G.X.hom b = _
    rw [pullbackComparison_hom_fst]
    change pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst, baseChangeIdIso_hom_left]
  · exact (Over.w ((baseChange b).mapIso
        (baseChangeIdIso G)).hom.hom.hom).trans
      (Over.w (pullbackComparison (𝟙 S) b b (Category.comp_id _) G).hom.hom.hom).symm

/-- A semilinear map towards the group gives transport from the identity pullback. -/
def semilinearComponent {S : Scheme.{u}} (G : GroupScheme S) {b : S ⟶ S}
    (e : (baseChange b).obj G ≅ G) :
    (baseChange (𝟙 S)).obj G ≅ (baseChange b).obj G :=
  baseChangeIdIso G ≪≫ e.symm

/-- The usual tower law for semilinear maps gives normalized component composition. -/
theorem semilinearComponent_comp {S : Scheme.{u}} (G : GroupScheme S)
    {b c d : S ⟶ S} (hbc : b ≫ c = d)
    (eb : (baseChange b).obj G ≅ G) (ec : (baseChange c).obj G ≅ G)
    (ed : (baseChange d).obj G ≅ G)
    (he : pullbackComparison c b d hbc G ≪≫ ed =
      (baseChange b).mapIso ec ≪≫ eb) :
    (semilinearComponent G eb).hom ≫
      pullHom b (Category.comp_id _) hbc (semilinearComponent G ec).hom =
      (semilinearComponent G ed).hom := by
  have hid : (pullbackComparison (𝟙 S) b b (Category.comp_id _) G).inv ≫
      (baseChange b).map (baseChangeIdIso G).hom = 𝟙 _ := by
    rw [← baseChangeIdIso_comparison]
    exact Iso.inv_hom_id _
  have hinv := congrArg (fun e => e.inv) he
  change ed.inv ≫ (pullbackComparison c b d hbc G).inv =
    eb.inv ≫ (baseChange b).map ec.inv at hinv
  simp only [semilinearComponent, Iso.trans_hom, Iso.symm_hom, pullHom,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc (pullbackComparison (𝟙 S) b b (Category.comp_id _) G).inv,
    hid, Category.id_comp, ← Category.assoc eb.inv, ← hinv]
  simp

section TripleProjections
variable {B S : Scheme.{u}} (p : S ⟶ B) {I : Type}
    (q : I → (S ⟶ Overlap p)) [∀ i, IsIso (q i ≫ fst p)]

@[reassoc (attr := simp)] theorem tripleComponent_p12 (i j : I) :
    tripleComponent p q (i, j) ≫ p12 p = q i := by
  simp [tripleComponent, componentPullbackMap, p12, pullback.map]

@[reassoc (attr := simp)] theorem tripleComponent_p23 (i j : I) :
    tripleComponent p q (i, j) ≫ p23 p =
      (q i ≫ snd p) ≫ inv (q j ≫ fst p) ≫ q j := by
  simp [tripleComponent, componentPullbackMap, p23, Category.assoc,
    pullback.map]

end TripleProjections

namespace SemilinearComponents
variable {B S : Scheme.{u}} (p : S ⟶ B) {I : Type}
    (q : I → (S ⟶ Overlap p))
    [∀ i, IsIso (q i ≫ fst p)]
    (b : I → (S ⟶ S))
    (hf : ∀ i, q i ≫ fst p = 𝟙 S) (hg : ∀ i, q i ≫ snd p = b i)
    (m : I → I → I) (hm : ∀ i j, b i ≫ b j = b (m i j))

include hf in
theorem triple_p1 (i j : I) :
    tripleComponent p q (i, j) ≫ p1 p = 𝟙 S := by
  simp [hf]

include hg in
theorem triple_p2 (i j : I) :
    tripleComponent p q (i, j) ≫ p2 p = b i := by
  change tripleComponent p q (i, j) ≫ p12 p ≫ snd p = _
  rw [← Category.assoc, tripleComponent_p12, hg]

include hf hg hm in
theorem triple_p3 (i j : I) :
    tripleComponent p q (i, j) ≫ p3 p = b (m i j) := by
  simp [hf, hg, hm]

include hf hg in
theorem triple_p23 (i j : I) :
    tripleComponent p q (i, j) ≫ p23 p = b i ≫ q j := by
  simp [hf, hg]

include hf hg hm in
theorem triple_p13 (i j : I) :
    tripleComponent p q (i, j) ≫ p13 p = q (m i j) := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, p13_fst] using
      (triple_p1 p q hf i j).trans (hf (m i j)).symm
  · simpa only [Category.assoc, p13_snd] using
      (triple_p3 p q b hf hg m hm i j).trans (hg (m i j)).symm

variable (G : GroupScheme S)
    (a : ∀ i, (baseChange (𝟙 S)).obj G ≅ (baseChange (b i)).obj G)
    [Finite I] [IsIso (Sigma.desc q)]

/-- Assemble the actual overlap isomorphism from its normalized components. -/
def overlap : OverlapIso p G :=
  FiniteComponents.pullbackIsoAlong q hf hg a

omit [∀ i, IsIso (q i ≫ fst p)] in
@[simp] theorem pullIso_overlap (i : I) :
    pullIso (q i) (hf i) (hg i) (overlap p q b hf hg G a) = a i :=
  FiniteComponents.pullIso_pullbackIsoAlong q hf hg a i

omit [∀ i, IsIso (q i ≫ fst p)] in
@[simp] theorem pullHom_overlap (i : I) :
    pullHom (q i) (hf i) (hg i) (overlap p q b hf hg G a).hom = (a i).hom :=
  congrArg (fun e => e.hom) (pullIso_overlap p q b hf hg G a i)

/-- Componentwise semilinear composition implies the actual triple-overlap cocycle. -/
theorem cocycle
    (ha : ∀ i j, (a i).hom ≫
      pullHom (b i) (Category.comp_id _) (hm i j) (a j).hom = (a (m i j)).hom) :
    Cocycle (overlap p q b hf hg G a) := by
  apply FiniteComponents.pullHom_ext_along (tripleComponent p q)
    (fun ij => triple_p1 p q hf ij.1 ij.2)
    (fun ij => triple_p3 p q b hf hg m hm ij.1 ij.2)
  rintro ⟨i, j⟩
  rw [pullHom_comp _ _ (triple_p2 p q b hg i j)]
  change pullHom _ _ _ (pullHom (p12 p) rfl rfl _) ≫
      pullHom _ _ _ (pullHom (p23 p) (p23_fst p) rfl _) =
    pullHom _ _ _ (pullHom (p13 p) (p13_fst p) (p13_snd p) _)
  rw [pullHom_pullHom, pullHom_pullHom, pullHom_pullHom]
  rw [pullHom_congr_map (tripleComponent_p12 p q i j) (hf i) (hg i)]
  rw [pullHom_congr_map (triple_p23 p q b hf hg i j)
    ((Category.assoc _ _ _).trans (by rw [hf j]; simp))
    ((Category.assoc _ _ _).trans (by rw [hg j]; exact hm i j))]
  rw [pullHom_congr_map (triple_p13 p q b hf hg m hm i j)
    (hf (m i j)) (hg (m i j))]
  rw [← pullHom_pullHom (q j) (b i) (hf j) (hg j)
    (Category.comp_id _) (hm i j)]
  simpa only [pullHom_overlap] using ha i j

/-- Actual Čech descent data from the supplied coherent family. -/
def datum
    (ha : ∀ i j, (a i).hom ≫
      pullHom (b i) (Category.comp_id _) (hm i j) (a j).hom = (a (m i j)).hom) :
    Datum p G where
  overlap := overlap p q b hf hg G a
  cocycle := cocycle p q b hf hg m hm G a ha

/-- Build actual descent data directly from the usual semilinear tower law. -/
def datumOfSemilinear
    (e : ∀ i, (baseChange (b i)).obj G ≅ G)
    (he : ∀ i j, pullbackComparison (b j) (b i) (b (m i j)) (hm i j) G ≪≫ e (m i j) =
      (baseChange (b i)).mapIso (e j) ≪≫ e i) :
    Datum p G :=
  datum p q b hf hg m hm G (fun i => semilinearComponent G (e i))
    (fun i j => semilinearComponent_comp G (hm i j) (e i) (e j) (e (m i j)) (he i j))

@[simp] theorem pullIso_datumOfSemilinear
    (e : ∀ i, (baseChange (b i)).obj G ≅ G)
    (he : ∀ i j, pullbackComparison (b j) (b i) (b (m i j)) (hm i j) G ≪≫ e (m i j) =
      (baseChange (b i)).mapIso (e j) ≪≫ e i) (i : I) :
    pullIso (q i) (hf i) (hg i)
        (datumOfSemilinear p q b hf hg m hm G e he).overlap =
      semilinearComponent G (e i) :=
  pullIso_overlap p q b hf hg G (fun i => semilinearComponent G (e i)) i

end SemilinearComponents

end Langlands.GroupScheme.Descent
