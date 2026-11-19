# Occurrence counts for paired rows

This is an internal finite-set calculation for the real compact model.
A row configuration records the subsets indexing a product of minors.
Its signed frequency on a rotation plane is the difference between the
occurrence counts of that plane's two rows.

For each choice of one row from each pair, form the nested family whose
level \(t\) contains exactly the rows with prescribed count greater than
\(t\). Row exchanges identify the level sizes for all choices. Double
counting the incidences of rows and levels gives a total equal to the
sum of the prescribed pair weights and singleton counts. Each pair's
total count bounds the absolute value of its frequency. Therefore, when
all absolute frequencies and singleton counts reach their prescribed
lower bounds, every one of these inequalities is an equality. Each pair
has its full weight on one row. The nested-family uniqueness lemma then
identifies the configuration with the corresponding canonical family.
