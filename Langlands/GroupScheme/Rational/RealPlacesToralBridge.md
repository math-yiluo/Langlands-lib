# Toral representatives at the real places

`realPlacesToralRepresentatives` proves `RealPlacesToralRepresentativesStatement`
in every universe. For a finite separable cover with a family of real-place
cocycles, it takes the splitting field of `X² + 1` over the covering field.
This is a finite separable extension of the number field and contains a square
root of `-1`. The tower inclusion gives one refinement for the whole family.

At each real place, the group over the completion is connected reductive by
field extension. The proof uses the completion's equivalence with `ℝ` and the
chosen square root to apply `toralRepresentative_realBaseChange_of_quadratic`
with the published `quadraticToralRepresentatives`. This gives a cocycle of a
maximal torus whose image is cohomologous to the refined local cocycle. This
refinement argument supplies the first premise of
`simplyConnectedRealPlacesSurjectivity_of_tori`.
