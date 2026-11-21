import Langlands.Geometry.FormalGroup.Tangent

/-! # Finite powers of a one-dimensional formal law -/

noncomputable section

namespace Langlands.FormalGroup

open CoordinateMap

universe u v

variable {R : Type u} [CommRing R]
variable {I σ : Type} [Finite I] [Finite σ]

namespace CoordinateMap

omit [Finite σ]

/-- Project the coordinate indexed by `i` to a one-coordinate space. -/
def copyProjection (i : I) : CoordinateMap R I Unit := vars fun _ => i

/-- Assemble one-coordinate maps with the same source into a tuple. -/
def toCopies (f : I → CoordinateMap R σ Unit) : CoordinateMap R σ I where
  series i := (f i).series ()
  constantCoeff_eq_zero i := (f i).constantCoeff_eq_zero ()

@[simp]
theorem copyProjection_comp_series (i : I) (f : CoordinateMap R σ I) (j : Unit) :
    ((copyProjection i).comp f).series j = f.series i :=
  MvPowerSeries.subst_X f.hasSubst i

@[simp]
theorem copyProjection_toCopies (i : I) (f : I → CoordinateMap R σ Unit) :
    (copyProjection i).comp (toCopies f) = f i := by
  apply CoordinateMap.ext
  funext j
  cases j
  exact copyProjection_comp_series i (toCopies f) ()

/-- The coordinate projections jointly detect equality of pointed maps. -/
theorem ext_copyProjection {f g : CoordinateMap R σ I}
    (h : ∀ i, (copyProjection i).comp f = (copyProjection i).comp g) : f = g := by
  apply CoordinateMap.ext
  funext i
  have hi := congrArg (fun k : CoordinateMap R σ Unit => k.series ()) (h i)
  simpa only [copyProjection_comp_series] using hi

end CoordinateMap

namespace CommLaw

variable (G : CommLaw R Unit) (I)

private def copiesAddition : CoordinateMap R (I ⊕ I) I :=
  CoordinateMap.toCopies fun i => G.addition.comp
    (((CoordinateMap.copyProjection i).comp fst).pair ((CoordinateMap.copyProjection i).comp snd))

private def copiesInverse : CoordinateMap R I I :=
  CoordinateMap.toCopies fun i => G.inverse.comp (CoordinateMap.copyProjection i)

private theorem projection_copiesAddition (i : I) :
    (CoordinateMap.copyProjection i).comp (copiesAddition I G) = G.addition.comp
      (((CoordinateMap.copyProjection i).comp fst).pair ((CoordinateMap.copyProjection i).comp snd)) :=
  CoordinateMap.copyProjection_toCopies _ _

omit [Finite σ] in
private theorem projection_copiesAddition_comp (i : I) (f : CoordinateMap R σ (I ⊕ I)) :
    (CoordinateMap.copyProjection i).comp ((copiesAddition I G).comp f) =
      G.addition.comp (((CoordinateMap.copyProjection i).comp (fst.comp f)).pair
        ((CoordinateMap.copyProjection i).comp (snd.comp f))) := by
  rw [← CoordinateMap.comp_assoc, projection_copiesAddition, CoordinateMap.comp_assoc, pair_comp]
  simp only [CoordinateMap.comp_assoc]

/-- A finite product of copies of a one-dimensional law in its product coordinates. -/
def copies : CommLaw R I where
  addition := copiesAddition I G
  inverse := copiesInverse I G
  zero_add := by
    apply CoordinateMap.ext_copyProjection
    intro i
    let p : CoordinateMap R I Unit := CoordinateMap.copyProjection i
    have h := congrArg (fun f : CoordinateMap R Unit Unit => f.comp p) G.zero_add
    simp only [CoordinateMap.comp_assoc, pair_comp, zero_comp, id_comp] at h
    simpa only [projection_copiesAddition_comp, fst_pair, snd_pair, comp_zero, comp_id] using h
  add_zero := by
    apply CoordinateMap.ext_copyProjection
    intro i
    let p : CoordinateMap R I Unit := CoordinateMap.copyProjection i
    have h := congrArg (fun f : CoordinateMap R Unit Unit => f.comp p) G.add_zero
    simp only [CoordinateMap.comp_assoc, pair_comp, zero_comp, id_comp] at h
    simpa only [projection_copiesAddition_comp, fst_pair, snd_pair, comp_zero, comp_id] using h
  add_assoc := by
    apply CoordinateMap.ext_copyProjection
    intro i
    let p : CoordinateMap R I Unit := CoordinateMap.copyProjection i
    let x : CoordinateMap R ((I ⊕ I) ⊕ I) Unit := p.comp (fst.comp fst)
    let y : CoordinateMap R ((I ⊕ I) ⊕ I) Unit := p.comp (snd.comp fst)
    let z : CoordinateMap R ((I ⊕ I) ⊕ I) Unit := p.comp snd
    have h := congrArg (fun f : CoordinateMap R ((Unit ⊕ Unit) ⊕ Unit) Unit =>
      f.comp ((x.pair y).pair z)) G.add_assoc
    simp only [CoordinateMap.comp_assoc, pair_comp, fst_pair, snd_pair] at h
    simpa only [projection_copiesAddition_comp, fst_pair, snd_pair] using h
  add_comm := by
    apply CoordinateMap.ext_copyProjection
    intro i
    let p : CoordinateMap R I Unit := CoordinateMap.copyProjection i
    have h := congrArg (fun f : CoordinateMap R (Unit ⊕ Unit) Unit =>
      f.comp ((p.comp (fst (τ := I))).pair (p.comp snd))) G.add_comm
    simp only [CoordinateMap.comp_assoc, pair_comp, fst_pair, snd_pair] at h
    simpa only [projection_copiesAddition_comp, projection_copiesAddition, fst_pair, snd_pair] using h
  neg_add := by
    apply CoordinateMap.ext_copyProjection
    intro i
    let p : CoordinateMap R I Unit := CoordinateMap.copyProjection i
    have h := congrArg (fun f : CoordinateMap R Unit Unit => f.comp p) G.neg_add
    simp only [CoordinateMap.comp_assoc, pair_comp, id_comp, zero_comp] at h
    simpa only [projection_copiesAddition_comp, fst_pair, snd_pair, comp_id, comp_zero,
      copiesInverse, CoordinateMap.copyProjection_toCopies] using h

namespace Hom

variable {G I}

/-- A projection from the product is a formal group homomorphism. -/
def copyProjection (i : I) : Hom (G.copies I) G where
  toCoordinateMap := CoordinateMap.copyProjection i
  map_add := projection_copiesAddition I G i

/-- Formal maps to the product assemble from maps to its factors. -/
def toCopies {H : CommLaw R σ} (f : I → Hom H G) : Hom H (G.copies I) where
  toCoordinateMap := CoordinateMap.toCopies fun i => (f i).toCoordinateMap
  map_add := by
    apply CoordinateMap.ext_copyProjection
    intro i
    rw [← CoordinateMap.comp_assoc, CoordinateMap.copyProjection_toCopies]
    let F := CoordinateMap.toCopies fun k => (f k).toCoordinateMap
    change (f i).toCoordinateMap.comp H.addition =
      (CoordinateMap.copyProjection i).comp ((copiesAddition I G).comp ((F.comp fst).pair (F.comp snd)))
    rw [projection_copiesAddition_comp, fst_pair, snd_pair]
    dsimp only [F]
    simp only [← CoordinateMap.comp_assoc, CoordinateMap.copyProjection_toCopies]
    exact (f i).map_add

@[simp]
theorem copyProjection_comp_toCopies {H : CommLaw R σ} (i : I) (f : I → Hom H G) :
    (copyProjection i).comp (toCopies f) = f i := by
  apply Hom.ext
  exact CoordinateMap.copyProjection_toCopies _ _

/-- Equality of formal maps to the product is detected on the factors. -/
theorem ext_copyProjection {H : CommLaw R σ} {f g : Hom H (G.copies I)}
    (h : ∀ i, (copyProjection i).comp f = (copyProjection i).comp g) : f = g := by
  apply Hom.ext
  exact CoordinateMap.ext_copyProjection fun i => congrArg Hom.toCoordinateMap (h i)

/-- The product endomorphism which acts separately on each factor. -/
def diagonal (f : I → Hom G G) : Hom (G.copies I) (G.copies I) :=
  toCopies fun i => (f i).comp (copyProjection i)

@[simp]
theorem copyProjection_comp_diagonal (f : I → Hom G G) (i : I) :
    (copyProjection i).comp (diagonal f) = (f i).comp (copyProjection i) :=
  copyProjection_comp_toCopies _ _

/-- Diagonal actions are multiplicative for actual formal composition. -/
def diagonalRingHom : (I → Hom G G) →+* Hom (G.copies I) (G.copies I) where
  toFun := diagonal
  map_zero' := by
    apply ext_copyProjection
    intro i
    rw [copyProjection_comp_diagonal, comp_zero]
    exact zero_comp _
  map_one' := by
    apply ext_copyProjection
    intro i
    rw [copyProjection_comp_diagonal]
    exact (id_comp _).trans (comp_id _).symm
  map_add' f g := by
    apply ext_copyProjection
    intro i
    rw [copyProjection_comp_diagonal, comp_add, copyProjection_comp_diagonal,
      copyProjection_comp_diagonal]
    exact add_comp _ _ _
  map_mul' f g := by
    apply ext_copyProjection
    intro i
    change (copyProjection i).comp (diagonal (f * g)) =
      (copyProjection i).comp ((diagonal f).comp (diagonal g))
    rw [copyProjection_comp_diagonal, ← Hom.comp_assoc, copyProjection_comp_diagonal,
      Hom.comp_assoc, copyProjection_comp_diagonal]
    exact Hom.comp_assoc _ _ _

/-- The tangent matrix of the diagonal formal action has the tangent scalars on its diagonal. -/
theorem diagonal_linearCoeff (f : I → Hom G G) (i j : I) :
    (diagonal f).toCoordinateMap.linearCoeff i j =
      scalarLinearCoeff ((f i).toCoordinateMap.linearCoeff () ()) i j := by
  classical
  change (((f i).toCoordinateMap).comp (CoordinateMap.copyProjection i)).linearCoeff () j = _
  rw [CoordinateMap.linearCoeff_comp]
  by_cases hj : j = i <;>
    simp [CoordinateMap.linearCoeff, CoordinateMap.copyProjection, scalarLinearCoeff,
      MvPowerSeries.coeff_index_single_X, hj]

end Hom
end CommLaw

namespace ModuleLaw

variable {O : Type v} [CommRing O] [Algebra O R]
variable (M : ModuleLaw O R Unit) (I)

/-- The finite product with the componentwise scalar action. -/
def copies : ModuleLaw O R I where
  groupLaw := M.groupLaw.copies I
  action := CommLaw.Hom.diagonalRingHom.comp
    { toFun := fun a _ => M.action a
      map_zero' := funext fun _ => M.action.map_zero
      map_one' := funext fun _ => M.action.map_one
      map_add' := fun a b => funext fun _ => M.action.map_add a b
      map_mul' := fun a b => funext fun _ => M.action.map_mul a b }
  linear_natural a i j := by
    change (CommLaw.Hom.diagonal fun _ : I => M.action a).toCoordinateMap.linearCoeff i j = _
    rw [CommLaw.Hom.diagonal_linearCoeff, M.linear_natural]
    simp [scalarLinearCoeff]

end ModuleLaw
end Langlands.FormalGroup
