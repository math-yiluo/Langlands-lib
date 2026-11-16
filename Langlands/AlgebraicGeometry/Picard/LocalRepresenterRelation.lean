import Langlands.AlgebraicGeometry.Picard.LocalRepresenterOverlap

/-! # The equivalence relation of a local presheaf representer -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.LocalRepresenter

variable {S U : Scheme.{u}} (p : U ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ Type v} {M : Over U}
    (e : ((Over.map p).op ⋙ F).RepresentableBy M)

/-- The overlap viewed over the original base. -/
abbrev overlapOverS : Over S := (Over.map p).obj (overlapOver p (M := M))

/-- The second projection over the original base. -/
abbrev secondOverS : overlapOverS p (M := M) ⟶ chart p (M := M) :=
  (Over.map p).map (secondOver p e)

/-- The two chart projections have the same original-base coordinate. -/
theorem projections_base : first p ≫ M.hom ≫ p = second p e ≫ M.hom ≫ p := by
  change pullback.fst (M.hom ≫ p) p ≫ (M.hom ≫ p) =
    (secondOver p e).left ≫ (M.hom ≫ p)
  rw [pullback.condition, ← Category.assoc, (secondOver p e).w]
  rfl

/-- The two projections of any test point classify the same family. -/
theorem kernel_w {T : Over S} (r : T ⟶ overlapOverS p (M := M)) :
    F.map (r ≫ firstOver p).op (family p e) =
      F.map (r ≫ secondOverS p e).op (family p e) := by
  simpa using congrArg (F.map r.op) (family_eq p e)

/-- A pair of chart maps classifying the same family gives an overlap point. -/
def kernelLift {T : Over S} (a b : T ⟶ chart p (M := M))
    (_h : F.map a.op (family p e) = F.map b.op (family p e)) :
    T ⟶ overlapOverS p (M := M) :=
  Over.homMk (pullback.lift a.left (b.left ≫ M.hom)
    (by simpa [chart, Category.assoc] using a.w.trans b.w.symm))
    (by
      change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ p = T.hom
      rw [pullback.lift_snd]
      simpa [chart, Category.assoc] using b.w)

@[simp]
theorem kernelLift_first {T : Over S} (a b : T ⟶ chart p (M := M))
    (h : F.map a.op (family p e) = F.map b.op (family p e)) :
    kernelLift p e a b h ≫ firstOver p = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[simp]
theorem kernelLift_second {T : Over S} (a b : T ⟶ chart p (M := M))
    (h : F.map a.op (family p e) = F.map b.op (family p e)) :
    kernelLift p e a b h ≫ secondOverS p e = b := by
  let T' : Over U := Over.mk (b.left ≫ M.hom)
  let c : (Over.map p).obj T' ⟶ T := Over.homMk (𝟙 T.left)
    (by
      change 𝟙 T.left ≫ T.hom = (b.left ≫ M.hom) ≫ p
      simpa [chart, Category.assoc] using b.w.symm)
  let b' : T' ⟶ M := Over.homMk b.left rfl
  have hc : c ≫ b = (Over.map p).map b' := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  have hh : F.map (c ≫ a).op (family p e) = e.homEquiv b' := by
    rw [e.homEquiv_eq]
    change F.map (c ≫ a).op (family p e) =
      F.map ((Over.map p).map b').op (family p e)
    rw [← hc]
    simpa using congrArg (F.map c.op) h
  have hs := congrArg Over.Hom.left (lift_second_of p e (c ≫ a) b' hh)
  apply Over.OverMorphism.ext
  exact hs

/-- The two chart projections determine an overlap point uniquely. -/
theorem kernel_hom_ext {T : Over S} {r r' : T ⟶ overlapOverS p (M := M)}
    (ht : r ≫ firstOver p = r' ≫ firstOver p)
    (hs : r ≫ secondOverS p e = r' ≫ secondOverS p e) : r = r' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg Over.Hom.left ht
  · have h := congrArg (fun f => f.left ≫ M.hom) hs
    change (r.left ≫ (secondOver p e).left) ≫ M.hom =
      (r'.left ≫ (secondOver p e).left) ≫ M.hom at h
    simpa only [Category.assoc, (secondOver p e).w, overlapOver, Over.mk_hom] using h

/-- Exchange the two chart projections. -/
def exchange : overlapOverS p (M := M) ⟶ overlapOverS p (M := M) :=
  kernelLift p e (secondOverS p e) (firstOver p) (family_eq p e).symm

@[simp]
theorem exchange_first : exchange p e ≫ firstOver p = secondOverS p e :=
  kernelLift_first p e _ _ _

@[simp]
theorem exchange_second : exchange p e ≫ secondOverS p e = firstOver p :=
  kernelLift_second p e _ _ _

@[simp]
theorem exchange_exchange : exchange p e ≫ exchange p e = 𝟙 _ := by
  apply kernel_hom_ext p e <;> simp [Category.assoc]

/-- The exchange map is an actual involutive scheme isomorphism. -/
def exchangeIso : overlap p (M := M) ≅ overlap p (M := M) :=
  (Over.forget S).mapIso
    { hom := exchange p e
      inv := exchange p e
      hom_inv_id := exchange_exchange p e
      inv_hom_id := exchange_exchange p e }

end Langlands.AlgebraicGeometry.Picard.LocalRepresenter
